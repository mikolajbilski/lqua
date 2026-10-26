from pathlib import Path
from enum import Enum
import subprocess
import colorama
import shutil
import sys

ROOT = Path(__file__).resolve().parent
TEST_FOLDER = ROOT / "tests"
PROGRAM = ROOT / "compiler.py"
TMP = ROOT / "tmp"
COMPOUT = TMP / "compout.s"
RUNTIME = ROOT / "runtime.c"
EXEC = TMP / "compout"

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
    expected_out = input_file.with_suffix(".out")

    if not expected_out.exists():
        print("Output file not found!")
        return TestResult.OTHER_ERROR

    result = None
    try:
        with open(COMPOUT, "w") as f:
            result = subprocess.run(
                ["uv", "run", str(PROGRAM), str(input_file)] + sys.argv[2:],
                cwd=ROOT,
                timeout=30,
                stdout=f
            )
    except subprocess.TimeoutExpired:
        print("Compilation timed out!")
        return TestResult.COMPILATION_FAIL

    if result.returncode != 0:
        return TestResult.COMPILATION_FAIL
    
    try:
        result = subprocess.run(
            ["gcc", "-g", "-o", str(EXEC), str(COMPOUT), str(RUNTIME), "-Wl,-z,noexecstack"],
            cwd=ROOT,
            timeout=30,
        )
    except subprocess.TimeoutExpired:
        print("GCC timed out!")
        return TestResult.GCC_FAIL

    if result.returncode != 0:
        return TestResult.GCC_FAIL

    stdin_file = input_file.with_suffix(".stdin")

    try:
        if stdin_file.exists():
            with open(stdin_file, "r") as stdin:
                result = subprocess.run(
                    [str(EXEC)],
                    cwd=ROOT,
                    timeout=30,
                    capture_output=True,
                    stdin=stdin
                )
        else:
            result = subprocess.run(
                [str(EXEC)],
                cwd=ROOT,
                timeout=30,
                capture_output=True,
            )
    except subprocess.TimeoutExpired:
        print("Final program timed out!")
        return TestResult.BAD_EXIT

    if result.returncode != 0:
        return TestResult.BAD_EXIT

    expected = expected_out.read_text().rstrip("\n")
    actual = result.stdout.decode("utf-8").rstrip("\n")

    if not expected == str(actual):
        print("Expected:")
        print(expected)
        print("Actual:")
        print(actual)
        return TestResult.BAD_RESULT
    
    return TestResult.SUCCESS

def main():
    TMP.mkdir(parents=True, exist_ok=True)
    test_files = sorted(TEST_FOLDER.rglob("*.in"))
    successes = 0
    fails = 0
    for test in test_files:
        test_name = test.relative_to(TEST_FOLDER).with_suffix("")
        result = run_test(test)
        result_msg = ""
        if result is TestResult.SUCCESS:
            result_msg = colorama.Fore.GREEN + "PASS"
        else:
            result_msg = colorama.Fore.RED + "FAIL"
        print(f"{test_name}: {result_msg}" + colorama.Style.RESET_ALL)
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

    shutil.rmtree(TMP)

if __name__ == "__main__":
    main()