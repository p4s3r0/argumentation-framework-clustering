import z3

from utils import Argument
from . import SemanticHelper 
from functools import reduce

class ConflictFreeSolver:
    def __init__(self, AF: dict[str, Argument.Argument]) -> None:
        '''
        @AF ->        Argumentation Framework
        '''
        self.AF = AF
        self.solution = []
        self.solver = z3.Solver()
        self.setRulesConflictFree()



    def setRulesConflictFree(self):
        ''' Sets the rules for admissibility check. Formula is in the Readme'''
        # get a: a∈A
        a: Argument.Argument
        for a in self.AF.values():

            if not a.is_singleton or len(a.defends) == 0:
                continue
            

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                if b.is_singleton:
                    self.solver.add(z3.Not(z3.And(a.z3_value, b.z3_value)))


        # skip empty set solution in calculation but add by hand
        clause = False
        for arg in self.AF.values():
            clause = z3.Or(clause, arg.z3_value)
        self.solver.add(clause)
        self.solution.append([])
        


    def computeSets(self, solution_amount: int=-1, algorithm: str="BFS"):
        return SemanticHelper.computeSets(self, solution_amount, algorithm)



    def verifySet(self, verify_set: list):
        return SemanticHelper.verifySet(self, verify_set)
    


    def negateSolutions(self, solution: list):
        solution_names = [sol.name for sol in solution]
        clause = False
        for arg in self.AF.keys():
            if arg not in solution_names:
                clause = z3.Or(clause, self.AF[arg].z3_value)

        self.solver.add(clause)



def solutionRefinement(solution: list):
    subsets = reduce(lambda result, x: result + [subset + [x] for subset in result], solution, [[]])
    subsets.pop(0)
    return subsets


