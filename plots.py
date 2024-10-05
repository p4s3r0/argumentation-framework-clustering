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


def plotRefinementVSNoRef(tests, title, ax):
    # REF vs NOREF ----------------------------------------------------------------------------------------
    ref   = sortTests([t for t in tests if t.refinement == False and t.DFS_BFS == "BFS"])
    noref = sortTests([t for t in tests if t.refinement == True and t.DFS_BFS == "BFS"])

    for i, x in enumerate(ref): x.index = i
    for i, x in enumerate(noref): x.index = i

    ref_line,   = ax.plot([x.index for x in ref],   [y.runtime for y in ref],   linewidth=2.0, label='ref')
    noref_line, = ax.plot([x.index for x in noref], [y.runtime for y in noref], linewidth=2.0, label='no-ref')

    ax.set_title(title)
    print("ref:", len(ref)," - noref:", len(noref))



def sortEqualTests(a, b):
    a_out = list()
    b_out = list()
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

    random_bfs = [t for t in random if t.DFS_BFS == "BFS"]
    random_dfs = [t for t in random if t.DFS_BFS == "DFS"]
    random_bfs, random_dfs = sortEqualTests(random_bfs, random_dfs)

    grid_bfs = [t for t in grid if t.DFS_BFS == "BFS"]
    grid_dfs = [t for t in grid if t.DFS_BFS == "DFS"]
    grid_bfs, grid_dfs = sortEqualTests(grid_bfs, grid_dfs)

    level_bfs = [t for t in level if t.DFS_BFS == "BFS"]
    level_dfs = [t for t in level if t.DFS_BFS == "DFS"]
    level_bfs, level_dfs = sortEqualTests(level_bfs, level_dfs)

    ax.scatter([t.runtime for t in random_bfs], [t.runtime for t in random_dfs], marker='+', label='random')
    ax.scatter([t.runtime for t in grid_bfs], [t.runtime for t in grid_dfs], marker='o', label='grid')
    ax.scatter([t.runtime for t in level_bfs], [t.runtime for t in level_dfs], marker='*', label='level')



def plotBFSvsDFS(tests, title, ax):
    # BFS vs DFS ------------------------------------------------------------------------------------------
    bfs = sortTests([t for t in tests if t.refinement == True and t.DFS_BFS == "BFS"])
    dfs = sortTests([t for t in tests if t.refinement == True and t.DFS_BFS == "DFS"])

    for i, x in enumerate(bfs): x.index = i
    for i, x in enumerate(dfs): x.index = i

    bfs_line, = ax.plot([x.index for x in bfs], [y.runtime for y in bfs], linewidth=2.0, label='bfs')
    dfs_line, = ax.plot([x.index for x in dfs], [y.runtime for y in dfs], linewidth=2.0, label='dfs')

    ax.set_title(title)
    print("bfs:", len(bfs)," - dfs:", len(dfs))



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



def main():



    random_ST = readInTestFiles("input/experiment/tests-run/faithful/ST/results_faithful_random-based.txt")
    grid_ST = readInTestFiles("input/experiment/tests-run/faithful/ST/results_faithful_grid-based.txt")
    level_ST = readInTestFiles("input/experiment/tests-run/faithful/ST/results_faithful_level-based.txt")

    random_AD = readInTestFiles("input/experiment/tests-run/faithful/AD/results_faithful_random-based.txt")
    grid_AD = readInTestFiles("input/experiment/tests-run/faithful/AD/results_faithful_grid-based.txt")
    level_AD = readInTestFiles("input/experiment/tests-run/faithful/AD/results_faithful_level-based.txt")

    random_CF = readInTestFiles("input/experiment/tests-run/faithful/CF/results_faithful_random-based.txt")
    grid_CF = readInTestFiles("input/experiment/tests-run/faithful/CF/results_faithful_grid-based.txt")
    level_CF = readInTestFiles("input/experiment/tests-run/faithful/CF/results_faithful_level-based.txt")



    fig, ax = plt.subplots(3, 3)
    # STABLE
    plotBFSvsDFS(random_ST, "random ST ", ax[0][0])
    plotBFSvsDFS(grid_ST, "grid ST ", ax[1][0])
    plotBFSvsDFS(level_ST, "level ST ", ax[2][0])
    # ADMISSIBLE
    plotBFSvsDFS(random_AD, "random AD ", ax[0][1])
    plotBFSvsDFS(grid_AD, "grid AD ", ax[1][1])
    plotBFSvsDFS(level_AD, "level AD ", ax[2][1])
    # CONFLICT-FREE
    plotBFSvsDFS(random_CF, "random CF", ax[0][2])
    plotBFSvsDFS(grid_CF, "grid CF", ax[1][2])
    plotBFSvsDFS(level_CF, "grid CF", ax[2][2])
    # SETTINGS
    fig.suptitle('BFS vs DFS')
    handles, labels = ax[0][0].get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')


    fig, ax = plt.subplots(3, 3)
    # STABLE
    plotRefinementVSNoRef(random_ST, "random ST", ax[0][0])
    plotRefinementVSNoRef(grid_ST, "grid ST", ax[1][0])
    plotRefinementVSNoRef(level_ST, "level ST", ax[2][0])
    # ADMISSIBLE
    plotRefinementVSNoRef(random_AD, "random AD", ax[0][1])
    plotRefinementVSNoRef(grid_AD, "grid AD", ax[1][1])
    plotRefinementVSNoRef(level_AD, "level AD", ax[2][1])
    # CONFLICT-FREE
    plotRefinementVSNoRef(random_CF, "random CF", ax[0][2])
    plotRefinementVSNoRef(grid_CF, "grid CF", ax[1][2])
    plotRefinementVSNoRef(level_CF, "level CF", ax[2][2])
    # SETTINGS
    fig.suptitle('REF vs NO-REF')
    handles, labels = ax[0][0].get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')

 
    fig, ax = plt.subplots(1)
    plotSemantics({"CF": random_CF + grid_CF + level_CF,
                   "AD": random_AD + grid_AD + level_AD,
                   "ST": random_ST + grid_ST + level_ST},"Semantics", ax)
    # SETTINGS
    fig.suptitle('Semantics')
    handles, labels = ax.get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')




    fig, ax = plt.subplots(1)
    # STABLE
    plotKaktusBFSandDFS({"random": random_AD + random_ST,
                   "grid": grid_AD + grid_ST,
                   "level":  level_AD + level_ST}, ax)
    # SETTINGS
    fig.suptitle('Kaktus Plot faithful check. x=BFS y=DFS')
    handles, labels = ax.get_legend_handles_labels()
    fig.legend(handles, labels, loc='right')

    plt.show()

    



if __name__ == "__main__":
    main()



