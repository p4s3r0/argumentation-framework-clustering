import subprocess
import colorama
import os
import time
import psutil
import gc

EXP = f"{colorama.Fore.BLUE}[EXP]{colorama.Style.RESET_ALL}"
EXP_OK = f"{colorama.Fore.GREEN}[EXP]{colorama.Style.RESET_ALL}"
EXP_TEST = f"{colorama.Fore.LIGHTBLACK_EX}[EXP]{colorama.Style.RESET_ALL}"

testcases_path = "input/experiment"


class TestBench:
    def __init__(self) -> None:
        self.random_based_path = f"{testcases_path}/random-based"
        self.random_based_testcases = list()
        self.grid_based_path = f"{testcases_path}/grid-based"
        self.grid_based_testcases = list()
        self.level_based_path = f"{testcases_path}/level-based"
        self.level_based_testcases = list()

class Testcase:
    def __init__(self, concrete, abstract) -> None:
        self.concrete = concrete
        self.abstract = abstract




def init_testcases():
    test_bench = TestBench()
    #random
    temp = os.listdir(f"{test_bench.random_based_path}/concrete")
    for t in temp:
        test = Testcase(f"{test_bench.random_based_path}/concrete/{t}", f"{test_bench.random_based_path}/abstract/{t}")
        test_bench.random_based_testcases.append(test)

    #grid
    temp = os.listdir(f"{test_bench.grid_based_path}/concrete")
    for t in temp:
        test = Testcase(f"{test_bench.grid_based_path}/concrete/{t}", f"{test_bench.grid_based_path}/abstract/{t}")
        test_bench.grid_based_testcases.append(test)


    #level
    temp = os.listdir(f"{test_bench.level_based_path}/concrete")
    for t in temp:
        test = Testcase(f"{test_bench.level_based_path}/concrete/{t}", f"{test_bench.level_based_path}/abstract/{t}")
        test_bench.level_based_testcases.append(test)


    return test_bench




def extract_data_faithful(res, com):
    split_data = res.split("\n")
    temp = list()
    for line in split_data:
        line = line.replace('\n', '')
        line = line.replace('\x1b[90m', '')
        line = line.replace('[SPECS]   ', '')
        line = line.replace('Runtime:     ','')
        line = line.replace('CPU-Time:    ','')
        line = line.replace('Memory RSS:  ','')
        line = line.replace(' s', '')
        line = line.replace(' MB', '')
        line = line.replace('\x1b[0m', '')
        temp.append(line)

    if len(temp) < 5:
        print("\n", temp, com, end="\n\n")
        data = {
            "result": "TIMEOUT",
            "runtime": "X",
            "cpu_time": "X",
            "memory": "X"
        }
        return data

    data = {
        "result": temp[0],
        "runtime": temp[1],
        "cpu_time": temp[2],
        "memory": temp[3]
    }
    return data


def getDataFromFile(test):
    ret = list()
    with open(test, 'r') as f:
        for line in f:
            if line.find(':') == -1:
                continue
            line = line.replace("# ", '')
            line = line.replace('\n', '')
            line = line.replace(' ', '')
            line = line.split(':')
            ret.append(line)
    return ret



def writeTestResultToFile(data):
    with open(f"input/experiment/results_concretize.txt", 'a') as f:
        f.write(f"{data['timestamp']};")
        f.write(f"{data['program']};")
        f.write(f"{data['semantics']};")
        f.write(f"{data['DFS/BFS']};")
        f.write(f"{data['refinement']};")
        f.write(f"{data['approach']};")
        f.write(f"{data['arg_amount']};")
        f.write(f"{data['p']};")
        f.write(f"X;")
        f.write(f"{data['input_file_concrete']};")
        f.write(f"{data['att_amount']};")
        f.write(f"{data['input_file_abstract']};")
        f.write(f"{data['result']};")
        f.write(f"{data['runtime']};")
        f.write(f"{data['cpu_time']};")
        f.write(f"{data['memory']};\n")



def extractData(test, timeout, result, refinement, semantics, BFSDFS, program, com):
    data = dict()
    if not timeout:
        data = extract_data_faithful(result, com)
    else:
        data["result"] = "TIMEOUT"
        data["runtime"] = "X"
        data["cpu_time"] = "X"
        data["memory"] = "X"

    data["test"] = test.concrete
    data["timestamp"] = time.strftime("%D %T", time.gmtime(time.time()))
    data["program"] = program
    data["semantics"] = semantics
    data["DFS/BFS"] = BFSDFS
    data["refinement"] = refinement

    temp = getDataFromFile(test.concrete)
    for d in temp:
        data[d[0]] = d[1]
    data["input_file_concrete"] = test.concrete
    data["input_file_abstract"] = test.abstract
    writeTestResultToFile(data)


def RUN_TEST_FAITHFUL(tests, generator_approach, BFS_DFS, semantics, refinement):
    print(f"{EXP} Starting prog=CHECK gen={generator_approach} {BFS_DFS} {semantics} ref={refinement}")

    for i, test in enumerate(tests):
        command = f"python3 main.py CHECK {test.abstract} -c {test.concrete} -exp -a {BFS_DFS} -s {semantics}"

        command = ["python3", "main.py", "CHECK", test.abstract, "-c", test.concrete, "-exp", "-a", BFS_DFS, "-s", semantics]
        if not refinement: command.append("-noref")
        print(f"{EXP_TEST} Running Test {i+1}/{len(tests)} {test.concrete}", end="\r")
        try:
            process = subprocess.Popen(command, stdout=subprocess.
            PIPE, stderr=subprocess.PIPE, text=True)
            stdout, stderr = process.communicate(timeout=300)
            result = stdout

            os.system(f"kill {process.pid} > /dev/null 2>&1")
            extractData(test, False, result, refinement=refinement, semantics=semantics, BFSDFS=BFS_DFS, program="CHECK", com=command)
        except subprocess.TimeoutExpired:
            os.system(f"kill {process.pid} > /dev/null 2>&1")
            extractData(test, True, None, refinement=refinement, semantics=semantics, BFSDFS=BFS_DFS, program="CHECK", com=command)

        gc.collect()
    print(f"\n{EXP_OK} Finished Successfully")




def RUN_TEST_CONCRETIZE(tests, generator_approach, BFS_DFS, semantics, refinement):
    print(f"{EXP} Starting prog=CONCRETIZE gen={generator_approach} {BFS_DFS} {semantics} ref={refinement}")
    for i, test in enumerate(tests):
        concretize_arguments = list()
        with open(test.abstract, 'r') as f:
            f.readline(); f.readline();
            concretize = f.readline().split()
            if concretize[1] != "concretize:":
                print("something wrong with concretize line of", test.abstract)
            concretize_arguments = concretize[2:]

        command = ["python3", "main.py", "CONCRETIZE", test.abstract, "-c", test.concrete, "-exp", "-a", BFS_DFS, "-s", semantics, "-p"]
        for arg in concretize_arguments:
            command.append(arg)
        if not refinement: command.append("-noref")
        print(f"{EXP_TEST} Running Test {i+1}/{len(tests)} {test.concrete}", end="\r")
        try:
            process = subprocess.Popen(command, stdout=subprocess.
            PIPE, stderr=subprocess.PIPE, text=True)
            stdout, stderr = process.communicate(timeout=300)
            result = stdout

            os.system(f"kill {process.pid} > /dev/null 2>&1")
            extractData(test, False, result, refinement=refinement, semantics=semantics, BFSDFS=BFS_DFS, program="CHECK", com=command)
        except subprocess.TimeoutExpired:
            os.system(f"kill {process.pid} > /dev/null 2>&1")
            extractData(test, True, None, refinement=refinement, semantics=semantics, BFSDFS=BFS_DFS, program="CHECK", com=command)

        gc.collect()
    print(f"\n{EXP_OK} Finished Successfully")


def main():
    test_bench = init_testcases()
    do_tests = False
    # FAITHFUL ---------------------------------------------------------
    for approach in ["random-based"]:
        for BFS_or_DFS in ["BFS", "DFS"]:
            for semantics in ["AD"]:
                for refinement in [True, False]:
                    tests = None
                    if approach == "random-based":
                        tests = test_bench.random_based_testcases
                    elif approach == "grid-based":
                        tests = test_bench.grid_based_testcases
                    else:
                        tests = test_bench.level_based_testcases

                    #RUN_TEST_FAITHFUL(tests, approach, BFS_or_DFS, semantics, refinement)
                    RUN_TEST_CONCRETIZE(tests, approach, BFS_or_DFS, semantics, refinement)

    # CONCRETIZE ------------------------------------------------------







if __name__ == "__main__":
    main()