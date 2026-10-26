from pathlib import Path
from enum import Enum
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PROGRAM = ROOT / "compiler.py"
OUT = ROOT / "out"
COMPOUT = OUT / "compout.s"
RUNTIME = ROOT / "runtime.c"
EXEC = OUT / "compout"

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

def compile_and_run(input_file: Path, compiler_opts: list[str]) -> TestResult:

    result = None
    try:
        with open(COMPOUT, "w") as f:
            result = subprocess.run(
                ["uv", "run", str(PROGRAM), str(input_file)] + compiler_opts,
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
                    stdin=stdin
                )
        else:
            result = subprocess.run(
                [str(EXEC)],
                cwd=ROOT,
                timeout=30,
            )
    except subprocess.TimeoutExpired:
        print("Final program timed out!")
        return TestResult.BAD_EXIT

    if result.returncode != 0:
        return TestResult.BAD_EXIT
    
    return TestResult.SUCCESS

def main():
    if len(sys.argv) < 2:
        print(f"usage: {sys.argv[0]} <input_file> [compiler_options]")
    test_path = ROOT / sys.argv[1]
    OUT.mkdir(parents=True, exist_ok=True)
    result = compile_and_run(test_path, sys.argv[2:])
    if result is not TestResult.SUCCESS:
        print(error_messages[result] + "!")

if __name__ == "__main__":
    main()