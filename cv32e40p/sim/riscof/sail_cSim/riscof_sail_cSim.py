import os
import re
import shutil
import subprocess
import shlex
import logging
import random
import string
from string import Template
import distutils

import riscof.utils as utils
from riscof.pluginTemplate import pluginTemplate
import riscof.constants as constants
from riscv_isac.isac import isac

logger = logging.getLogger()

class sail_cSim(pluginTemplate):
    __model__ = "sail_c_simulator"
    __version__ = "0.5.0"

    docker_cmd = 'docker run -w /work -v {0}:/work -a stdout -a stderr --init {1} {2}'

    def __init__(self, *args, **kwargs):
        sclass = super().__init__(*args, **kwargs)

        config = kwargs.get('config')
        if config is None:
            logger.error("Config node for sail_cSim missing.")
            raise SystemExit(1)
        self.num_jobs = str(config['jobs'] if 'jobs' in config else 1)

        if 'docker' in config and config['docker']=='True':
            self.docker = True
        else:
            self.docker = False

        self.docker_img = str(config['image']) if 'image' in config else 'riscv_compliance'
        self.pluginpath = os.path.abspath(config['pluginpath'])
        path = config['PATH'] if 'PATH' in config else ""

        self.sail_exe = { '32' : os.path.join(path,"riscv_sim_RV32"), '64' : os.path.join(path,"riscv_sim_RV64")}
        self.isa_spec = os.path.abspath(config['ispec']) if 'ispec' in config else ''
        self.platform_spec = os.path.abspath(config['pspec']) if 'ispec' in config else ''
        self.make = config['make'] if 'make' in config else 'make'
        logger.debug("SAIL CSim plugin initialised using the following configuration.")
        if 'target_run' in config and config['target_run']=='0':
            self.target_run = False
        else:
            self.target_run = True
        for entry in config:
            logger.debug(entry+' : '+config[entry])
        return sclass

    def initialise(self, suite, work_dir, archtest_env):
        self.suite = suite
        self.work_dir = work_dir
        self.objdump_cmd = 'riscv{1}-unknown-elf-objdump -D {0} > {2};'
        self.archtest_env = archtest_env
        compile_cmd = 'riscv{1}-unknown-elf-gcc -march={0} \
         -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles'

        if not self.docker:
            compile_cmd += ' -T '+self.pluginpath+'/env/link.ld\
                -I '+self.pluginpath+'/env/\
                -I ' + archtest_env
        else:
            compile_cmd += ' -T /work/sail_work/env/link.ld\
                -I /work/sail_work/env/\
                -I /work/test/includes'
        self.compile_cmd = compile_cmd
            
    def build(self, isa_yaml, platform_yaml):
        ispec = utils.load_yaml(isa_yaml)['hart0']
        self.xlen = ('64' if 64 in ispec['supported_xlen'] else '32')
        self.isa = 'rv' + self.xlen
        self.compile_cmd = self.compile_cmd+' -mabi='+('lp64 ' if 64 in ispec['supported_xlen'] else 'ilp32 ')
        if "I" in ispec["ISA"]:
            self.isa += 'i'
        if "M" in ispec["ISA"]:
            self.isa += 'm'
        if "F" in ispec["ISA"]:
            self.isa += 'f'
        if "C" in ispec["ISA"]:
            self.isa += 'c'
        if "D" in ispec["ISA"]:
            self.isa += 'd'
        if "Zicsr" in ispec["ISA"]:
            self.isa += '_zicsr'
        if "Zifencei" in ispec["ISA"]:
            self.isa += '_zifencei'

        if "hw_data_misaligned_support" in ispec and ispec["hw_data_misaligned_support"]== True:
            self.enable_data_misaligned = '--enable-misaligned'
        else:
            self.enable_data_misaligned = ''

        objdump = "riscv{0}-unknown-elf-objdump".format(self.xlen)

        if not self.docker:
            if shutil.which(objdump) is None:
                logger.error(objdump+": executable not found. Please check environment setup.")
                raise SystemExit(1)
            compiler = "riscv{0}-unknown-elf-gcc".format(self.xlen)
            if shutil.which(compiler) is None:
                logger.error(compiler+": executable not found. Please check environment setup.")
                raise SystemExit(1)
            if shutil.which(self.sail_exe[self.xlen]) is None:
                logger.error(self.sail_exe[self.xlen]+ ": executable not found. Please check environment setup.")
                raise SystemExit(1)
            if shutil.which(self.make) is None:
                logger.error(self.make+": executable not found. Please check environment setup.")
                raise SystemExit(1)
        else:
            os.mkdir(os.path.join(self.work_dir,"sail_work"))
            os.mkdir(os.path.join(self.work_dir,"test"))
            self.test_dir = os.path.join(self.work_dir,"test")
            distutils.dir_util.copy_tree(self.archtest_env,os.path.join(self.test_dir,"includes"))
            distutils.dir_util.copy_tree(
                    os.path.join(self.pluginpath,"env"),
                    os.path.join(self.work_dir,"sail_work/env"))


    def runTests(self, testList, cgf_file=None):
        make = utils.makeUtil(makefilePath=os.path.join(self.work_dir, "Makefile." + self.name[:-1]))
        if self.docker:
            dmake = utils.makeUtil(makefilePath=os.path.join(self.work_dir, "Makefile.docker." + self.name[:-1]))
            dmake.makeCommand = self.make + ' -d -j' + self.num_jobs
        make.makeCommand = self.make + ' -d -j' + self.num_jobs
        for file in testList:
            testentry = testList[file]
            test = testentry['test_path']
            test_dir = testentry['work_dir']
            test_name = test.rsplit('/',1)[1][:-2]

            sig_file = self.name[:-1] + ".signature"

            if self.docker:
                dest = os.path.join(self.test_dir,test_name+".S")
                shutil.copyfile(test,dest)
                test = dest.replace(self.work_dir,"/work")
                test_dir = test_dir.replace(self.work_dir,"/work")
            
            elf = 'ref.elf'

            execute = "@cd "+ test_dir +";"

            cmd = self.compile_cmd.format(self.isa, self.xlen) + ' ' + test + ' -o ' + elf
            compile_cmd = cmd + ' -D' + " -D".join(testentry['macros'])
            execute+=compile_cmd+";"

            execute += self.objdump_cmd.format(elf, self.xlen, 'ref.disass')

            if 'c' not in  self.isa:
                cmd = self.sail_exe[self.xlen]+' -C'
            else:
                cmd = self.sail_exe[self.xlen]

            if self.docker:
                execute += cmd + ' {0} --test-signature={1} {2} > {3}.log 2>&1;'.format(self.enable_data_misaligned, sig_file, elf, test_name)
            else:
                execute += cmd + ' {0} --test-signature={1} {2} > {3}.log;'.format(self.enable_data_misaligned, sig_file, elf, test_name)

            cov_str = ' '
            for label in testentry['coverage_labels']:
                cov_str+=' -l '+label

            if cgf_file is not None:
                coverage_cmd = 'riscv_isac --verbose info coverage -d \
                        -t {0}.log --parser-name c_sail -o coverage.rpt  \
                        --sig-label begin_signature  end_signature \
                        --test-label rvtest_code_begin rvtest_code_end \
                        -e ref.elf -c {1} -x{2} {3};'.format(\
                        test_name, ' -c '.join(cgf_file), self.xlen, cov_str)
            else:
                coverage_cmd = ''

            if not self.docker:
                execute+=coverage_cmd
            make.add_target(execute,tname=test_name)

            # Need to increase the default short timeout
            self.timeout = 20000

            if self.docker:
                dexecute = self.docker_cmd.format(self.work_dir,self.docker_img,'make -f /work/'+
                    "Makefile." + self.name[:-1]+" "+test_name)
                if coverage_cmd:
                    dexecute+=";cd "+testentry['work_dir']+";"+coverage_cmd
                dmake.add_target(dexecute,tname=test_name)
        if self.target_run:
            if self.docker:
                dmake.execute_all(self.work_dir, self.timeout)
            else:
                make.execute_all(self.work_dir, self.timeout)
        else:
          #raise SystemExit(0)
          print("No target to Run")

