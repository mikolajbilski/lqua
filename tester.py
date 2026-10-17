from pathlib import Path
from enum import Enum
import subprocess
import os
import colorama

ROOT = Path(__file__).resolve().parent
TEST_FOLDER = ROOT / "tests"
PROGRAM = ROOT / "tester.py"

class TestResult(Enum):
    SUCCESS = 0
    COMPILATION_FAIL = 1
    GCC_FAIL = 2
    BAD_EXIT = 3
    BAD_RESULT = 4
    OTHER_ERROR = 5

error_messages = {
    TestResult.COMPILATION_FAIL: "Compilation failed",
    TestResult.GCC_FAIL: "GCC failed",
    TestResult.BAD_EXIT: "Program exited with non-zero exit code",
    TestResult.BAD_RESULT: "Bad test output",
    TestResult.OTHER_ERROR: "An unexpected error occured",
}

def run_test(input_file: Path) -> TestResult:
    return TestResult.SUCCESS

def main():
    test_files = sorted(TEST_FOLDER.rglob("*.in"))
    successes = 0
    fails = 0
    for test in test_files:
        test_name = str(test)[len(str(TEST_FOLDER)) + 1:-3]
        print(f"{test_name}: ", end="")
        result = run_test(test)
        result_msg = ""
        if result is TestResult.SUCCESS:
            result_msg = colorama.Fore.GREEN + "PASS"
        else:
            result_msg = colorama.Fore.RED + "FAIL"
        print(result_msg + colorama.Style.RESET_ALL)
        if result is  TestResult.SUCCESS:
            successes += 1
        else:
            fails += 1
            print(error_messages[result] + "!")
    print(f"\nTests run: {successes + fails}")
    print(f"Passed: {successes}")
    print(f"Failed: {fails}")
    if fails == 0:
        print("All tests successful!")

if __name__ == "__main__":
    main()