from . import file_tests
from . import os_linux_tests
from . import os_windows_tests
from . import memory_tests


def handle_test(module, test):
    print(test + "\t", end="")
    try:
        getattr(module, test)()
        print("OK")
    except Exception as e:
        print("ERROR")
        # raise e


def handle_module(module_name, module):
    print(module_name)
    for test in dir(module):
        if "test" in test:
            handle_test(module, test)


def run():
    handle_module("memory tests", memory_tests)
    handle_module("file tests", file_tests)
    handle_module("os linux tests", os_linux_tests)
    handle_module("os windows tests", os_windows_tests)
