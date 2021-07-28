import logging
import importlib
import os

l = logging.getLogger(name=__name__)

from . import FakeSimProcedure

def auto_import_packages(base_module, base_path, ignore_dirs=(), ignore_files=(), scan_modules=True):
    for lib_module_name in os.listdir(base_path):
        if lib_module_name in ignore_dirs or lib_module_name == '__pycache__':
            continue

        lib_path = os.path.join(base_path, lib_module_name)
        init_path = os.path.join(lib_path, '__init__.py')
        if not os.path.isfile(init_path):
            l.debug("Not a module: %s", lib_module_name)
            continue

        l.debug("Loading %s.%s", base_module, lib_module_name)

        try:
            package = importlib.import_module(".%s" % lib_module_name, base_module)
        except ImportError:
            l.warning("Unable to autoimport package %s.%s", base_module, lib_module_name, exc_info=True)
        else:
            if scan_modules:
                for name, mod in auto_import_modules('%s.%s' % (base_module, lib_module_name), lib_path, ignore_files=ignore_files):
                    if name not in dir(package):
                        setattr(package, name, mod)
            yield lib_module_name, package

def auto_import_modules(base_module, base_path, ignore_files=()):
    for proc_file_name in os.listdir(base_path):
        if not proc_file_name.endswith('.py'):
            continue
        if proc_file_name in ignore_files or proc_file_name == '__init__.py':
            continue
        proc_module_name = proc_file_name[:-3]

        try:
            proc_module = importlib.import_module(".%s" % proc_module_name, base_module)
        except ImportError:
            l.warning("Unable to autoimport module %s.%s", base_module, proc_module_name, exc_info=True)
            continue
        else:
            yield proc_module_name, proc_module

def filter_module(mod, type_req=None, subclass_req=None):
    for name in dir(mod):
        val = getattr(mod, name)
        if type_req is not None and not isinstance(val, type_req):
            continue
        if subclass_req is not None and not issubclass(val, subclass_req):
            continue
        yield name, val

# Import all classes under the current directory, and group them based on
# lib names.
SIM_PROCEDURES = {}
path = os.path.dirname(os.path.abspath(__file__))
skip_dirs = ['definitions']

for pkg_name, package in auto_import_packages('.', path, skip_dirs):
    for _, mod in filter_module(package, type_req=type(os)):
        for name, proc in filter_module(mod, type_req=type, subclass_req=FakeSimProcedure):
            if hasattr(proc, "__provides__"):
                for custom_pkg_name, custom_func_name in proc.__provides__:
                    if custom_pkg_name not in SIM_PROCEDURES:
                        SIM_PROCEDURES[custom_pkg_name] = { }
                    SIM_PROCEDURES[custom_pkg_name][custom_func_name] = proc
            else:
                if pkg_name not in SIM_PROCEDURES:
                    SIM_PROCEDURES[pkg_name] = { }
                SIM_PROCEDURES[pkg_name][name] = proc
                if hasattr(proc, "ALT_NAMES") and proc.ALT_NAMES:
                    for altname in proc.ALT_NAMES:
                        SIM_PROCEDURES[pkg_name][altname] = proc
                if name == 'UnresolvableJumpTarget':
                    SIM_PROCEDURES[pkg_name]['UnresolvableTarget'] = proc
