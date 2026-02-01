import subprocess
import warnings
from subprocess import PIPE
import platform
import os


class Control:
    def __init__(self, address='127.0.0.1', port=4040):
        if 'DV_CONTROL_PATH' in os.environ:
            self._control_name = os.environ['DV_CONTROL_PATH']
        else:
            if (platform.system().upper().find("MINGW") != -1) or (platform.system() == "Windows"):
                self._control_name = "dv-control.exe"
            else:
                self._control_name = "dv-control"

        self._address = address
        self._port = str(port)

    def _communicate(self, command):
        proc = subprocess.Popen([self._control_name, '-i', self._address, '-p', self._port, '-s'] + command.split(' '),
                                stdout=PIPE,
                                stderr=PIPE)
        stdout, stderr = proc.communicate()
        error = stderr.decode('utf-8').strip() if stderr is not None else ''
        out = stdout.decode('utf-8').strip() if stdout is not None else ''
        exit_code = proc.returncode

        if exit_code != 0:
            raise RuntimeError('Could not perform action. exit code %d' % exit_code)

        if error.lower().startswith('error'):
            raise RuntimeError('Command "%s" failed with "%s"' % (command, error))
        return out

    def put(self, path, parameter, value, _legacy_value=None):
        if _legacy_value is not None:
            value = _legacy_value
            warnings.warn("put with value_type is deprecated. Use put(path, parameter, value) instead",
                          DeprecationWarning)

        if type(value) == bool:
            value = str(value).lower()
        self._communicate('put %s %s %s' % (path, parameter, str(value)))

    def set(self, path, parameter, value, _legacy_value=None):
        self.put(path, parameter, value, _legacy_value)

    def get(self, path, parameter, value_type=None):
        if value_type is not None:
            warnings.warn("get with value_type is deprecated. Use set(path, parameter) instead", DeprecationWarning)

        output = self._communicate('get %s %s' % (path, parameter))
        vt = self._communicate('get_type %s %s' % (path, parameter))
        if vt == 'int' or vt == 'long':
            return int(output)
        elif vt == 'float' or vt == 'double':
            return float(output)
        elif vt == 'bool':
            return output == 'true'
        return output

    def add_module(self, module_name, module_library):
        self._communicate('add_module %s %s' % (module_name, module_library))

    def remove_module(self, module_name):
        self._communicate('remove_module %s' % module_name)

    def node_exists(self, path):
        output = self._communicate('node_exists %s' % path)
        return output == 'true'

    def attribute_exists(self, path, parameter, value_type=None):
        if value_type is not None:
            warnings.warn(
                "attribute_exists with value_type is deprecated. Use attribute_exists(path, parameter) instead",
                DeprecationWarning)
        output = self._communicate('attr_exists %s %s' % (path, parameter))
        return output == 'true'

    def get_children(self, path):
        output = self._communicate('get_children %s' % path)
        return [] if output == '' else output.strip().split('|')
