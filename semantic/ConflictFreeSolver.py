import z3

from utils import Argument
from . import SemanticHelper 

class ConflictFreeSolver:
    def __init__(self, AF: dict[str, Argument.Argument]) -> None:
        '''
        @AF ->        Argumentation Framework
        '''
        self.AF = AF
        self.solution = list()
        self.solver = z3.Solver()
        self.setRulesConflictFree()



    def setRulesConflictFree(self):
        ''' Sets the rules for admissibility check. Formula is in the Readme'''
        # get a: a∈A
        a: Argument.Argument
        for a in self.AF.values():

            if not a.is_singleton:
                continue
            
            # check if b exists
            if len(a.defends) == 0:
                self.solver.add(z3.Implies(a.z3_value, True))
                continue

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                if b.is_singleton:
                    self.solver.add(z3.Not(z3.And(a.z3_value, b.z3_value)))
        

    def computeSets(self, solution_amount: int=-1, algorithm: str="BFS"):
        return SemanticHelper.computeSets(self, solution_amount, algorithm)


    def verifySet(self, verify_set: list):
        return SemanticHelper.verifySet(self, verify_set)
