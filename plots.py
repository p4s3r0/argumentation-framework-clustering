import matplotlib.pyplot as plt


timeout = 300
out_f = 0

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





def plotSemantics(test_runs, title):
    fig, ax = plt.subplots()

    data = {"CF": list(), "AD": list(), "ST": list()}
    for sem in ["CF", "AD", "ST"]:
        for gen in ["random-based", "grid-based", "level-based"]:
            for file in test_runs[gen]:
                    for DFS_BFS in ["BFS", "DFS"]:
                        for ref in ["True", "False"]:
                            if test_runs[gen][file][sem][DFS_BFS][ref].runtime < 300:
                                data[sem].append(test_runs[gen][file][sem][DFS_BFS][ref].runtime)
    data["CF"] = sorted(data["CF"])
    data["AD"] = sorted(data["AD"])
    data["ST"] = sorted(data["ST"])

    cf_line, = ax.plot(data["CF"], range(len(data["CF"])), linewidth=2.0, label='CF')
    ad_line, = ax.plot(data["AD"], range(len(data["AD"])), linewidth=2.0, label='AD')
    st_line, = ax.plot(data["ST"], range(len(data["ST"])), linewidth=2.0, label='ST')
    
    printForThesis(data["CF"], range(len(data["CF"])))
    printForThesis(data["AD"], range(len(data["AD"])))
    printForThesis(data["ST"], range(len(data["ST"])))

    ax.set_ylabel("Testrun numeration")
    ax.set_xlabel("Runtime [s]")
    ax.set_title(title)
    plt.show()


def plotSemanticsSplit(test_runs, title):
    fig, ax = plt.subplots()

    data = {"CF-F": list(), "CF-T": list(), "AD": list(), "ST": list()}
    for sem in ["CF", "AD", "ST"]:
        for gen in ["random-based", "grid-based", "level-based"]:
            for file in test_runs[gen]:
                    for DFS_BFS in ["BFS", "DFS"]:
                        for ref in ["True"]:
                            if sem == "CF":
                                if test_runs[gen][file][sem][DFS_BFS][ref].runtime < 300:
                                    data["CF-T"].append(test_runs[gen][file][sem][DFS_BFS]["True"].runtime)
                                    data["CF-F"].append(test_runs[gen][file][sem][DFS_BFS]["False"].runtime)

                            else:
                                if test_runs[gen][file][sem][DFS_BFS][ref].runtime < 300:
                                    data[sem].append(test_runs[gen][file][sem][DFS_BFS][ref].runtime)
    data["CF-T"] = sorted(data["CF-T"])
    data["CF-F"] = sorted(data["CF-F"])
    data["AD"] = sorted(data["AD"])
    data["ST"] = sorted(data["ST"])

    cfT_line, = ax.plot(data["CF-T"], range(len(data["CF-T"])), linewidth=2.0, label='CF-T')
    cfF_line, = ax.plot(data["CF-F"], range(len(data["CF-F"])), linewidth=2.0, label='CF-F')
    ad_line, = ax.plot(data["AD"], range(len(data["AD"])), linewidth=2.0, label='AD')
    st_line, = ax.plot(data["ST"], range(len(data["ST"])), linewidth=2.0, label='ST')
    
    ax.set_ylabel("Testrun numeration")
    ax.set_xlabel("Runtime [s]")
    ax.set_title(title)
    handles, labels = ax.get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')
    plt.show()


def readTestFile(test_runs, file_name):
    with open(file_name, 'r') as f:
        f.readline()
        for line in f:
            if line == '\n':
                continue
            line = line.split(';')
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
                data.append((test_runs[gen][file][sem]["BFS"]["True"], test_runs[gen][file][sem]["DFS"]["True"]))
                data.append((test_runs[gen][file][sem]["BFS"]["False"], test_runs[gen][file][sem]["DFS"]["False"]))
            # sort data over BFS runtime
            sorted_data = sorted(data, key=lambda t: (t[0].runtime, t[1].runtime))
            ax[y][x].plot([y[0].runtime for y in sorted_data], range(len(sorted_data)), linewidth=2.0, label='BFS')
            ax[y][x].plot([y[1].runtime for y in sorted_data], range(len(sorted_data)), linewidth=2.0, label='DFS')
            ax[y][x].set_ylabel("Testrun numeration")
            ax[y][x].set_xlabel("Runtime [s]")
            ax[y][x].set_title(f"{gen} {sem}")
            # printForThesis([y[0].runtime for y in sorted_data], range(len(sorted_data)))
            # printForThesis([y[1].runtime for y in sorted_data], range(len(sorted_data)))


    print("here")
    fig.suptitle(title)
    handles, labels = ax[0][0].get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')


def plotRefinementVSNoRef(test_runs, title):
    # REF vs NOREF ----------------------------------------------------------------------------------------
    fig, ax = plt.subplots(3, 3)
    for y, gen in enumerate(test_runs):
        for x, sem in enumerate(["CF", "AD", "ST"]):
            data = list()
            for file in test_runs[gen]:
                for BFS_DFS in ["BFS", "DFS"]:
                    data.append((test_runs[gen][file][sem][BFS_DFS]["True"], test_runs[gen][file][sem][BFS_DFS]["False"]))
            # sort data over BFS runtime
            sorted_data = sorted(data, key=lambda t: (t[0].runtime, t[1].runtime))

            if sem == "CF":
               printForThesis([y[0].runtime for y in sorted_data], range(len(sorted_data)))
               printForThesis([y[1].runtime for y in sorted_data], range(len(sorted_data)))

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

    printForThesis([y[0].runtime for y in data["random-based"]], [y[1].runtime for y in data["random-based"]])
    printForThesis([y[0].runtime for y in data["grid-based"]], [y[1].runtime for y in data["grid-based"]])
    printForThesis([y[0].runtime for y in data["level-based"]], [y[1].runtime for y in data["level-based"]])

    ax.set_ylabel("DFS Runtime [s]")
    ax.set_xlabel("BFS Runtime [s]")

    fig.suptitle(title)
    handles, labels = ax.get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')
    plt.show()



def plotRefinementSDirect(test_runs, title):
    fig, ax = plt.subplots()
    data = {"CF": list(), "AD": list(), "ST": list()}
    for gen in test_runs:
        for file in test_runs[gen]:
            for sem in ["CF", "AD", "ST"]:
                for ref in ["BFS", "DFS"]:
                    data[sem].append((test_runs[gen][file][sem][ref]["True"], test_runs[gen][file][sem][ref]["False"]))

    # sort data over BFS runtime
    data["CF"] = sorted(data["CF"], key=lambda t: (t[0].runtime, t[1].runtime))
    data["AD"] = sorted(data["AD"], key=lambda t: (t[0].runtime, t[1].runtime))
    data["ST"] = sorted(data["ST"], key=lambda t: (t[0].runtime, t[1].runtime))

    ax.scatter([y[0].runtime for y in data["CF"]], [y[1].runtime for y in data["CF"]], marker='+', label='conflict-free')
    ax.scatter([y[0].runtime for y in data["AD"]], [y[1].runtime for y in data["AD"]], marker='*', label='admissible')
    ax.scatter([y[0].runtime for y in data["ST"]], [y[1].runtime for y in data["ST"]], marker='o', label='stable')

    printForThesis([y[0].runtime for y in data["CF"]], [y[1].runtime for y in data["CF"]])
    printForThesis([y[0].runtime for y in data["AD"]], [y[1].runtime for y in data["AD"]])
    printForThesis([y[0].runtime for y in data["ST"]], [y[1].runtime for y in data["ST"]])


    ax.set_ylabel("NO-REF Runtime [s]")
    ax.set_xlabel("REF Runtime [s]")

    fig.suptitle(title)
    handles, labels = ax.get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')
    plt.show()



def calculateValues(test_runs):
    for sem in ["CF", "AD", "ST"]:
        runtime_per_arg = {
            "10": [0, 0, 0],
            "15": [0, 0, 0],
            "20": [0, 0, 0],
            "25": [0, 0, 0],
            "30": [0, 0, 0],
        }
        timeout_amount = 0
        tests_amount = 0

        for gen in ["random-based", "grid-based", "level-based"]:
            for file in test_runs[gen]:
                    for BFS_DFS in ["BFS", "DFS"]:
                        for ref in ["True", "False"]:
                            t = test_runs[gen][file][sem][BFS_DFS][ref]
                            if t.runtime == timeout:
                                runtime_per_arg[str(t.param_generator_arg_amount)][2] += 1
                                timeout_amount += 1
                            else:
                                runtime_per_arg[str(t.param_generator_arg_amount)][0] += t.runtime
                                runtime_per_arg[str(t.param_generator_arg_amount)][1] += 1
                            tests_amount += 1

        print(f"STATS for {sem}")
        for arg in runtime_per_arg:
            print(f"{arg}: {runtime_per_arg[arg][0]/runtime_per_arg[arg][1]:0.2f} (timeout: {runtime_per_arg[arg][2]}/{runtime_per_arg[arg][1]})")
        print(f"timeout: {timeout_amount}/{tests_amount}")




def printForThesis(x, y):
    global out_f
    out_f += 1
    with open(f"plot/out_plot_{out_f}.dat", "w") as f:
        f.write("x y\n")
        for i in range(len(x)):
            f.write(f"{x[i]} {y[i]}\n")



def plotBFSvsDFSspecial(test_runs, fai_tests_better, title):
    # BFS vs DFS  ----------------------------------------------------------------------------------------
    fig, ax = plt.subplots(2)
    for x, alg in enumerate(["BFS", "DFS"]):
        data_old = list()
        data_new = list()
        for gen in ["random-based", "grid-based", "level-based"]:
            for sem in ["CF", "AD", "ST"]:
                for file in test_runs[gen]:
                    data_old.append(test_runs[gen][file][sem][alg]["False"])
                    data_new.append(fai_tests_better[gen][file][sem][alg]["False"])
        
        sorted_data_old = sorted(data_old, key=lambda t: t.runtime)
        sorted_data_new = sorted(data_new, key=lambda t: t.runtime)
        ax[x].plot([y.runtime for y in sorted_data_old], range(len(sorted_data_old)), linewidth=2.0, label='old')
        ax[x].plot([y.runtime for y in sorted_data_new], range(len(sorted_data_new)), linewidth=2.0, label='new')
        ax[x].set_ylabel("Testrun numeration")
        ax[x].set_xlabel("Runtime [s]")
        ax[x].set_title(f"ye")
        printForThesis([y.runtime for y in sorted_data_old], range(len(sorted_data_old)))
        printForThesis([y.runtime for y in sorted_data_new], range(len(sorted_data_new)))


    fig.suptitle(title)
    handles, labels = ax[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')



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


    fai_tests_better = dict()
    readTestFile(fai_tests_better, "input/experiment/tests-run/with_optimization/results_faithful.txt")

    #plotBFSvsDFS(fai_tests_better, "better")
    #plotBFSvsDFS(fai_tests, "FAITHFUL program BFS vs DFS")
    plotBFSvsDFSspecial(fai_tests, fai_tests_better, "h")
    plt.show()

    exit()
    # plotBFSvsDFSDirect(fai_tests, "FAITHFUL program Scatter Plot BFS vs DFS")
    # plotRefinementVSNoRef(fai_tests, "FAITHFUL program REF vs NO-REF")
    # plotRefinementSDirect(fai_tests, "FAITHFUL program  Scatter Plot REF vs NO-REF")
    plotSemantics(fai_tests, "FAITHFUL, Runtime of Testruns per Semantic")
    #
    # calculateValues(fai_tests)





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


    # plotBFSvsDFS(con_tests, "CONCRETIZE program BFS vs DFS")
    # plotBFSvsDFSDirect(con_tests, "CONCRETIZE program Scatter Plot BFS vs DFS")
    # plotRefinementVSNoRef(con_tests, "CONCRETIZE program REF vs NO-REF")
    plotRefinementSDirect(con_tests, "CONCRETIZE program  Scatter Plot REF vs NO-REF")
    # plotSemanticsSplit(con_tests, "CONCRETIZE, Runtime of Testruns per Semantic")

    calculateValues(con_tests)





if __name__ == "__main__":
    main()



