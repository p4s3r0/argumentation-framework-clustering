import matplotlib.pyplot as plt


timeout = 300


class test:
    def __init__(self, timestamp, program, semantics, DFS_BFS, refinement, generator_approach, param_generator_arg_amount, param_generator_p, param_generator_level, input_file_concrete, input_file_concrete_attacks_amount, input_file_abstract, result, runtime, CPU_time, memory_consumption) -> None:
        self.index = None
        self.timestamp = timestamp
        self.program = program
        self.semantics = semantics
        self.DFS_BFS = DFS_BFS
        self.refinement = True if refinement=="True" else False
        self.generator_approach = generator_approach
        self.param_generator_arg_amount = int(param_generator_arg_amount)
        self.param_generator_p = param_generator_p
        self.param_generator_level = int(param_generator_level) if param_generator_level != 'X' else None
        self.input_file_concrete = input_file_concrete
        self.input_file_concrete_attacks_amount = input_file_concrete_attacks_amount
        self.input_file_abstract = input_file_abstract
        self.result = result if result != 'X' else None
        self.runtime = float(runtime) if runtime != 'X' else timeout
        self.CPU_time = float(CPU_time) if CPU_time != 'X' else None
        if memory_consumption == 'X' or memory_consumption == '\n':
            self.memory_consumption = None
        else:
            self.memory_consumption = float(memory_consumption)/1000



def readInTestFiles(filename):
    ret = list()
    with open(filename, 'r') as f:
        f.readline()
        for line in f:
            if line == '\n':
                continue
            line = line.split(';')
            ret.append(test(line[0], line[1], line[2], line[3], line[4], line[5], line[6], line[7], line[8], line[9], line[10], line[11], line[12], line[13], line[14], line[15]))
    return ret


def sortTests(tests):
    return sorted(tests, key=lambda x: (x.param_generator_arg_amount, x.input_file_concrete_attacks_amount))


def sortTestsRuntime(tests):
    return sorted(tests, key=lambda x: (x.runtime))






def sortEqualTests(a, b):
    a_out = list()
    b_out = list()

    print("as", len(a))

    for t in a:
        a_out.append(t)
        for t_ in b:
            if t_.input_file_concrete[39:] == t.input_file_concrete[39:] and t_.refinement == t.refinement:
                b_out.append(t_)
                break
    return a_out, b_out



def plotKaktusBFSandDFS(tests, ax):
    # BFS and DFS kaktus ------------------------------------------------------------------------------
    random = sortTests(tests["random"])
    grid = sortTests(tests["grid"])
    level = sortTests(tests["level"])


    random, grid = sortEqualTests(random, grid)
    print(len(random), len(grid))
    grid, level = sortEqualTests(grid, random)

    random_bfs = [t for t in random if t.DFS_BFS == "BFS"]
    random_dfs = [t for t in random if t.DFS_BFS == "DFS"]
    random_bfs, random_dfs = sortEqualTests(random_bfs, random_dfs)

    grid_bfs = [t for t in grid if t.DFS_BFS == "BFS"]
    grid_dfs = [t for t in grid if t.DFS_BFS == "DFS"]
    grid_bfs, grid_dfs = sortEqualTests(grid_bfs, grid_dfs)

    level_bfs = [t for t in level if t.DFS_BFS == "BFS"]
    level_dfs = [t for t in level if t.DFS_BFS == "DFS"]
    level_bfs, level_dfs = sortEqualTests(level_bfs, level_dfs)

    print(len(grid_bfs))

    ax.scatter([t.runtime for t in random_bfs], [t.runtime for t in random_dfs], marker='+', label='random')
    ax.scatter([t.runtime for t in grid_bfs], [t.runtime for t in grid_dfs], marker='o', label='grid')
    ax.scatter([t.runtime for t in level_bfs], [t.runtime for t in level_dfs], marker='*', label='level')

    ax.set_ylabel("Runtime BFS [s]")
    ax.set_xlabel("Runtime DFS [s]")




def plotSemantics(tests, title, ax):
    # Semantics ------------------------------------------------------------------------------------------
    cf = sortTestsRuntime(tests["CF"])
    ad = sortTestsRuntime(tests["AD"])
    st = sortTestsRuntime(tests["ST"])

    for i, x in enumerate(cf): x.index = i
    for i, x in enumerate(ad): x.index = i
    for i, x in enumerate(st): x.index = i

    cf_line, = ax.plot([x.index for x in cf], [y.runtime for y in cf], linewidth=2.0, label='CF')
    ad_line, = ax.plot([x.index for x in ad], [y.runtime for y in ad], linewidth=2.0, label='AD')
    st_line, = ax.plot([x.index for x in st], [y.runtime for y in st], linewidth=2.0, label='ST')

    print("cf:", len(cf)," - ad:", len(ad), " - st:", len(st))





def readTestFile(test_runs, file_name):
    with open(file_name, 'r') as f:
        f.readline()
        for line in f:
            if line == '\n':
                continue
            line = line.split(';')
            print(line)
            t = test(line[0], line[1], line[2], line[3], line[4], line[5], line[6], line[7], line[8], line[9], line[10], line[11], line[12], line[13], line[14], line[15])

            if t.generator_approach not in test_runs:
                test_runs[t.generator_approach] = dict()
            if t.input_file_concrete not in test_runs[t.generator_approach]:
                test_runs[t.generator_approach][t.input_file_concrete] = dict()
            if t.semantics not in test_runs[t.generator_approach][t.input_file_concrete]:
                test_runs[t.generator_approach][t.input_file_concrete][t.semantics] = dict()
            if t.DFS_BFS not in test_runs[t.generator_approach][t.input_file_concrete][t.semantics]:
                test_runs[t.generator_approach][t.input_file_concrete][t.semantics][t.DFS_BFS] = dict()
            if t.refinement not in test_runs[t.generator_approach][t.input_file_concrete][t.semantics][t.DFS_BFS]:
                test_runs[t.generator_approach][t.input_file_concrete][t.semantics][t.DFS_BFS][str(t.refinement)] = None

            test_runs[t.generator_approach][t.input_file_concrete][t.semantics][t.DFS_BFS][str(t.refinement)] = t





def plotBFSvsDFS(test_runs, title):
    # BFS vs DFS  ----------------------------------------------------------------------------------------
    fig, ax = plt.subplots(3, 3)
    for y, gen in enumerate(test_runs):
        for x, sem in enumerate(["CF", "AD", "ST"]):
            data = list()
            for file in test_runs[gen]:
                try:
                    data.append((test_runs[gen][file][sem]["BFS"]["True"], test_runs[gen][file][sem]["DFS"]["True"]))
                    data.append((test_runs[gen][file][sem]["BFS"]["False"], test_runs[gen][file][sem]["DFS"]["False"]))
                except:
                    print(gen, file, sem)
            # sort data over BFS runtime
            sorted_data = sorted(data, key=lambda t: (t[0].runtime, t[1].runtime))
            ax[y][x].plot([y[0].runtime for y in sorted_data], range(len(sorted_data)), linewidth=2.0, label='BFS')
            ax[y][x].plot([y[1].runtime for y in sorted_data], range(len(sorted_data)), linewidth=2.0, label='DFS')
            ax[y][x].set_ylabel("Testrun numeration")
            ax[y][x].set_xlabel("Runtime [s]")
            ax[y][x].set_title(f"{gen} {sem}")

    fig.suptitle(title)
    handles, labels = ax[0][0].get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')
    plt.show()



def plotRefinementVSNoRef(test_runs, title):
    # REF vs NOREF ----------------------------------------------------------------------------------------
    fig, ax = plt.subplots(3, 3)
    for y, gen in enumerate(test_runs):
        for x, sem in enumerate(["CF", "AD", "ST"]):
            data = list()
            for file in test_runs[gen]:
                for BFS_DFS in ["BFS", "DFS"]:
                    try:
                        data.append((test_runs[gen][file][sem][BFS_DFS]["True"], test_runs[gen][file][sem][BFS_DFS]["False"]))
                    except:
                        print(gen, file, sem)
            # sort data over BFS runtime
            sorted_data = sorted(data, key=lambda t: (t[0].runtime, t[1].runtime))
            ax[y][x].plot([y[0].runtime for y in sorted_data], range(len(sorted_data)), linewidth=2.0, label='REF')
            ax[y][x].plot([y[1].runtime for y in sorted_data], range(len(sorted_data)), linewidth=2.0, label='NO-REF')
            ax[y][x].set_xlabel("Runtime [s]")
            ax[y][x].set_ylabel("Testrun numeration")
            ax[y][x].set_title(f"{gen} {sem}")

    fig.suptitle(title)
    handles, labels = ax[0][0].get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')
    plt.show()




def plotBFSvsDFSDirect(test_runs, title):
    # KAKTUS BFS vs DFS ---------------------------------------------------------------------------------
    fig, ax = plt.subplots()
    data = {"random-based": list(), "grid-based": list(), "level-based": list()}
    for gen in test_runs:
        for sem in ["CF", "AD", "ST"]:
            for file in test_runs[gen]:
                data[gen].append((test_runs[gen][file][sem]["BFS"]["True"], test_runs[gen][file][sem]["DFS"]["True"]))
                data[gen].append((test_runs[gen][file][sem]["BFS"]["False"], test_runs[gen][file][sem]["DFS"]["False"]))

    # sort data over BFS runtime
    data["random-based"] = sorted(data["random-based"], key=lambda t: (t[0].runtime, t[1].runtime))
    data["grid-based"] = sorted(data["grid-based"], key=lambda t: (t[0].runtime, t[1].runtime))
    data["level-based"] = sorted(data["level-based"], key=lambda t: (t[0].runtime, t[1].runtime))

    ax.scatter([y[0].runtime for y in data["random-based"]], [y[1].runtime for y in data["random-based"]], marker='+', label='random')
    ax.scatter([y[0].runtime for y in data["grid-based"]], [y[1].runtime for y in data["grid-based"]], marker='+', label='grid')
    ax.scatter([y[0].runtime for y in data["level-based"]], [y[1].runtime for y in data["level-based"]], marker='+', label='level')


    fig.suptitle(title)
    handles, labels = ax.get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')
    plt.show()



def main():
    fai_tests = dict()
    readTestFile(fai_tests, "input/experiment/tests-run/faithful/ST/results_faithful_random-based.txt")
    readTestFile(fai_tests, "input/experiment/tests-run/faithful/ST/results_faithful_grid-based.txt")
    readTestFile(fai_tests, "input/experiment/tests-run/faithful/ST/results_faithful_level-based.txt")

    readTestFile(fai_tests, "input/experiment/tests-run/faithful/AD/results_faithful_random-based.txt")
    readTestFile(fai_tests, "input/experiment/tests-run/faithful/AD/results_faithful_grid-based.txt")
    readTestFile(fai_tests, "input/experiment/tests-run/faithful/AD/results_faithful_level-based.txt")

    readTestFile(fai_tests, "input/experiment/tests-run/faithful/CF/results_faithful_random-based.txt")
    readTestFile(fai_tests, "input/experiment/tests-run/faithful/CF/results_faithful_grid-based.txt")
    readTestFile(fai_tests, "input/experiment/tests-run/faithful/CF/results_faithful_level-based.txt")
    
    plotBFSvsDFS(fai_tests, "CONCRETIZE program BFS vs DFS")
    plotRefinementVSNoRef(fai_tests, "CONCRETIZE program REF vs NO-REF")
    plotBFSvsDFSDirect(fai_tests, "CONCRETIZE program Kaktus Plot BFS vs DFS")
    plt.show()

    exit()



    con_tests = dict()
    # CONCRETIZE ----------------------------------------------------
    readTestFile(con_tests, "input/experiment/tests-run/concretize/ST/results_concretize_random-based.txt")
    readTestFile(con_tests, "input/experiment/tests-run/concretize/ST/results_concretize_grid-based.txt")
    readTestFile(con_tests, "input/experiment/tests-run/concretize/ST/results_concretize_level-based.txt")

    readTestFile(con_tests, "input/experiment/tests-run/concretize/AD/results_concretize_random-based.txt")
    readTestFile(con_tests, "input/experiment/tests-run/concretize/AD/results_concretize_grid-based.txt")
    readTestFile(con_tests, "input/experiment/tests-run/concretize/AD/results_concretize_level-based.txt")

    readTestFile(con_tests, "input/experiment/tests-run/concretize/CF/results_concretize_random-based.txt")
    readTestFile(con_tests, "input/experiment/tests-run/concretize/CF/results_concretize_grid-based.txt")
    readTestFile(con_tests, "input/experiment/tests-run/concretize/CF/results_concretize_level-based.txt")


    #plotBFSvsDFS(con_tests, "CONCRETIZE program BFS vs DFS")
    #plotRefinementVSNoRef(con_tests, "CONCRETIZE program REF vs NO-REF")
    # plotBFSvsDFSDirect(con_tests, "CONCRETIZE program Kaktus Plot BFS vs DFS")
    plt.show()





if __name__ == "__main__":
    main()



