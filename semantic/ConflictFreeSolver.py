import z3

from utils import Argument
from utils import Solver


class ConflictFreeSolver:
    def __init__(self, AF: dict[str, Argument.Argument], algorithm: str) -> None:
        '''
        @AF ->        Argumentation Framework
        @semantic  -> "conflict_free" or "admissible"
        @algorithm -> "BFS"=(Breadth First Search) or "DFS"(Depth First Search)
        '''
        self.AF = AF
        self.algorithm = algorithm
        self.solution = list()
        self.solver = z3.Solver()
        self.setRulesConflictFree()



    # -----------------------------------------------------------------------------
    # Define clauses for admissible extensions
    def setRulesConflictFree(self):
        # get a: a∈A
        a: Argument.Argument
        for a in self.AF.values():

            if not a.is_singleton:
                continue
            
            # check if b exists
            if len(a.defends) == 0:
                self.solver.add(z3.Implies(a.z3_value, True))
                continue

            # (a -> ^{b:(b,a)∈R}(¬b)
            clause_left = True
            # (a -> ^{b:(b,a)∈R} (v{c:(c,b)∈R})))
            clause_right = True

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                if b.is_singleton:
                    self.solver.add(z3.Not(z3.And(a.z3_value, b.z3_value)))


    def computeSets(self):
        ''' Computes the defined Sets with the according algorithm '''
        if self.algorithm == "BFS":
            while model := Solver.solve(self.solver):
                self.solution.append(Solver.transformModelIntoArguments(arguments=self.AF, model=model))
                self.solver.add(Solver.negatePreviousModel(arguments=self.AF, model=model))
            else:
                return self.solution
            