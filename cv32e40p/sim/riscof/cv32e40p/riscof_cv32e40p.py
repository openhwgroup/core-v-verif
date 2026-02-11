import os
import re
import shutil
import subprocess
import shlex
import logging
import random
import string
from string import Template
import sys

import riscof.utils as utils
import riscof.constants as constants
from riscof.pluginTemplate import pluginTemplate

logger = logging.getLogger()

class cv32e40p(pluginTemplate):
    __model__ = "cv32e40p"
    __version__ = "1.2.0"

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        config = kwargs.get('config')

        # If the config node for this DUT is missing or empty. Raise an error. At minimum we need
        # the paths to the ispec and pspec files
        if config is None:
            print("Please enter input file paths in configuration.")
            raise SystemExit(1)

        # In case of an RTL based DUT, this would be point to the final binary executable of your
        # test-bench produced by a simulator (like verilator, vcs, incisive, etc). In case of an iss or
        # emulator, this variable could point to where the iss binary is located. If 'PATH variable
        # is missing in the config.ini we can hardcode the alternate here.
        #self.dut_exe = os.path.join(config['PATH'] if 'PATH' in config else "","cv32e40p")
        self.dut_exe = str(config['PATH'] if 'PATH' in config else "riscof")

        # Number of parallel jobs that can be spawned off by RISCOF
        # for various actions performed in later functions, specifically to run the tests in
        # parallel on the DUT executable. Can also be used in the build function if required.
        self.num_jobs = str(config['jobs'] if 'jobs' in config else 1)

        # Path to the directory where this python file is located. Collect it from the config.ini
        self.pluginpath=os.path.abspath(config['pluginpath'])

        # Collect the paths to the  riscv-config absed ISA and platform yaml files. One can choose
        # to hardcode these here itself instead of picking it from the config.ini file.
        self.isa_spec = os.path.abspath(config['ispec'])
        self.platform_spec = os.path.abspath(config['pspec'])

        self.tbpath=os.path.abspath(config['corevverifPATH'])

        if 'imperas_iss' in config and config['imperas_iss']=='yes':
            self.imperas_iss = 'yes'
        else:
            self.imperas_iss = 'no'

        self.dut_cfg = str(config['dut_cfg'] if 'dut_cfg' in config else 'default')

        self.sw_toolchain_prefix = str(config['sw_toolchain_prefix'] if 'sw_toolchain_prefix' in config else 'unknown')

        if 'enable_sim_cov' in config and config['enable_sim_cov']=='yes':
            self.enable_sim_cov = 'yes'
        else:
            self.enable_sim_cov = 'no'

        #We capture if the user would like the run the tests on the target or
        #not. If you are interested in just compiling the tests and not running
        #them on the target, then following variable should be set to False
        if 'target_run' in config and config['target_run']=='0':
            self.target_run = False
        else:
            self.target_run = True

        #check SIMULATOR env variable
        self.simulator_var = os.environ['SIMULATOR']

        supported_simulators = ['vsim', 'xrun', 'vcs']

        if self.simulator_var not in supported_simulators:
            print("Please set a supported SIMULATOR env variable before proceeding. Currently Supported : vsim, xrun, vcs")
            raise SystemExit(1)

    def initialise(self, suite, work_dir, archtest_env):

        # capture the working directory. Any artifacts that the DUT creates should be placed in this
        # directory. Other artifacts from the framework and the Reference plugin will also be placed
        # here itself.
        self.work_dir = work_dir

        # capture the architectural test-suite directory.
        self.suite_dir = suite

        # Note the march is not hardwired here, because it will change for each
        # test. Similarly the output elf name and compile macros will be assigned later in the
        # runTests function
        self.compile_cmd = 'riscv{1}-{2}-elf-gcc -march={0} \
          -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles \
          -T '+self.pluginpath+'/env/link.ld\
          -I '+self.pluginpath+'/env/\
          -I ' + archtest_env + ' {3} -o {4} {5}'


    def build(self, isa_yaml, platform_yaml):

        # load the isa yaml as a dictionary in python.
        ispec = utils.load_yaml(isa_yaml)['hart0']

        # capture the XLEN value by picking the max value in 'supported_xlen' field of isa yaml. This
        # will be useful in setting integer value in the compiler string (if not already hardcoded);
        self.xlen = ('64' if 64 in ispec['supported_xlen'] else '32')

        # for cv32e40p start building the '--isa' argument. the self.isa is dutnmae specific and may not be
        # useful for all DUTs
        self.isa = 'rv' + self.xlen
        if "I" in ispec["ISA"]:
            self.isa += 'i'
        if "M" in ispec["ISA"]:
            self.isa += 'm'
        if "F" in ispec["ISA"]:
            self.isa += 'f'
        if "D" in ispec["ISA"]:
            self.isa += 'd'
        if "C" in ispec["ISA"]:
            self.isa += 'c'
        if "Zicsr" in ispec["ISA"]:
            self.isa += '_zicsr'
        if "Zifencei" in ispec["ISA"]:
            self.isa += '_zifencei'

        self.compile_cmd = self.compile_cmd+' -mabi='+('lp64 ' if 64 in ispec['supported_xlen'] else 'ilp32 ')

    def runTests(self, testList):

        # Delete Makefile if it already exists.
        if os.path.exists(self.work_dir+ "/Makefile." + self.name[:-1]):
              os.remove(self.work_dir+ "/Makefile." + self.name[:-1])
        # create an instance the makeUtil class that we will use to create targets.
        make = utils.makeUtil(makefilePath=os.path.join(self.work_dir, "Makefile." + self.name[:-1]))

        # set the make command that will be used. The num_jobs parameter was set in the __init__
        # function earlier
        make.makeCommand = 'make -d -j' + self.num_jobs

        # we will iterate over each entry in the testList. Each entry node will be refered to by the
        # variable testname.
        for testname in testList:

            # for each testname we get all its fields (as described by the testList format)
            testentry = testList[testname]

            # we capture the path to the assembly file of this test
            test = testentry['test_path']

            # capture the directory where the artifacts of this test will be dumped/created. RISCOF is
            # going to look into this directory for the signature files
            test_dir = testentry['work_dir']
            test_name = test.rsplit('/',1)[1][:-2]

            # name of the elf file after compilation of the test
            elf = '{0}.elf'.format(test_name)

            # name of the signature file as per requirement of RISCOF. RISCOF expects the signature to
            # be named as DUT-<dut-name>.signature. The below variable creates an absolute path of
            # signature file.
            sig_file = os.path.join(test_dir, self.name[:-1] + ".signature")

            # for each test there are specific compile macros that need to be enabled. The macros in
            # the testList node only contain the macros/values. For the gcc toolchain we need to
            # prefix with "-D". The following does precisely that.
            compile_macros= ' -D' + " -D".join(testentry['macros'])

            # substitute all variables in the compile command that we created in the initialize
            # function
            test_compile_cmd = self.compile_cmd.format(self.isa, self.xlen, self.sw_toolchain_prefix, test, elf, compile_macros)
          
            #gen hex for simulation
            hex_cmd = 'riscv{0}-{1}-elf-objcopy -O verilog {2} {3}.hex'.format(self.xlen, self.sw_toolchain_prefix, elf, test_name)

            #gen readelf for simulation
            readelf_cmd = 'riscv{0}-{1}-elf-readelf -a {2} > {3}.readelf'.format(self.xlen, self.sw_toolchain_prefix, elf, test_name)

            #gen objdump for simulation
            objdmp_cmd = 'riscv{0}-{1}-elf-objdump -D -M no-aliases -S {2} > {3}.objdump'.format(self.xlen, self.sw_toolchain_prefix, elf, test_name)

            #gen objdump2itb for simulation
            objdmp2itb_cmd = 'riscv{0}-{1}-elf-objdump -d -S -M no-aliases -l {2} | '+self.tbpath+'/bin/objdump2itb - > {3}.itb'
            objdmp2itb_cmd = objdmp2itb_cmd.format(self.xlen, self.sw_toolchain_prefix, elf, test_name)

            # set up the simulation command
            simdir = 'cd {0}/cv32e40p/sim/{1}'.format(self.tbpath, self.dut_exe)
            simcmd = 'make riscof_sim_run TEST={0} USE_ISS={1} RISCOF_TEST_RUN_DIR={2} CFG={3} COV={4} SEED=random'.format(test_name, self.imperas_iss, testentry['work_dir'], self.dut_cfg, self.enable_sim_cov)

            #clean the build to save disk space during complete suite run
            if self.simulator_var == 'vsim':
                clean_work_dir_cmd = 'rm -rf {0}/work/'.format(testentry['work_dir'])
            elif self.simulator_var == 'xrun':
                clean_work_dir_cmd = 'rm -rf {0}/xcelium.d/'.format(testentry['work_dir'])
            elif self.simulator_var == 'vcs':
                clean_work_dir_cmd = 'rm -rf {0}/simv.daidir/'.format(testentry['work_dir'])
            else:
                simcmd = ''
                clean_work_dir_cmd = ''

            # concatenate all commands that need to be executed within a make-target.
            execute = '@cd {0}; {1}; {2}; {3}; {4}; {5}; {6}; {7}; {8}'.format(testentry['work_dir'], test_compile_cmd, hex_cmd, readelf_cmd, objdmp_cmd, objdmp2itb_cmd, simdir, simcmd, clean_work_dir_cmd)

            # create a target. The makeutil will create a target with the name "TARGET<num>" where num
            # starts from 0 and increments automatically for each new target that is added
            make.add_target(execute,tname=test_name)

            # Need to increase the default short timeout
            self.timeout = 20000

        # once the make-targets are done and the makefile has been created, run all the targets in
        # parallel using the make command set above.
        # if target runs are not required then we simply exit as this point after running all
        # the makefile targets.
        if self.target_run:
          make.execute_all(self.work_dir, self.timeout)
        else:
          #raise SystemExit(0)
          print("No target to Run")


