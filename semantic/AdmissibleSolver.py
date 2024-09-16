import z3

from utils import Argument
from . import SemanticHelper


class AdmissibleSolver:
    def __init__(self, AF: dict[str, Argument.Argument], AF_main: dict[str, Argument.Argument], no_refinement: bool) -> None:
        '''
        @AF ->        Argumentation Framework
        '''
        self.AF = AF
        self.AF_main = AF_main
        self.solution = list()
        self.solver = z3.Solver()
        self.no_refinement = no_refinement
        self.setRulesAdmissible()
        self.name = "CONC" if AF_main == None else "ABST"



    def setRulesAdmissible(self):
        ''' Sets the rules for admissibility check. Formula is in the Readme'''
        # get a: a∈A

        clause_cf = True
        a: Argument.Argument
        for a in self.AF.values():

            if not a.is_singleton or len(a.defends) == 0:
                continue

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                if b.is_singleton:
                    clause_cf = z3.And(clause_cf, (z3.Not(z3.And(a.z3_value, b.z3_value))))

        clause_right = True
        a: Argument.Argument
        for a in self.AF.values():

            if not a.is_singleton:
                continue

            if len(a.defends) == 0:
                clause_right = z3.And(clause_right, z3.Implies(a.z3_value, True))
                continue

            clause_right_and = True

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                if len(b.defends) == 0:
                    clause_right_and = False
                    break

                clause_right_or = False
                # get c: (c,b)∈R
                c: Argument.Argument
                for c in b.defends:
                    c = self.AF[c]
                    clause_right_or = z3.Or(clause_right_or, c.z3_value)
                clause_right_and = z3.And(clause_right_and, clause_right_or)

            clause_right = z3.And(clause_right, z3.Implies(a.z3_value, clause_right_and))

        clause = z3.And(clause_cf, clause_right)
        self.solver.add(clause)


        #### REFINEMENT ----------------------------------------------------------------
        if self.AF_main == None or self.no_refinement:
            return

        clause_cf = True
        a: Argument.Argument
        for a in self.AF_main.values():

            if not a.is_singleton or len(a.defends) == 0:
                continue

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF_main[b]

                if b.is_singleton:
                    clause_cf = z3.And(clause_cf, (z3.Not(z3.And(a.z3_value, b.z3_value))))

        clause_right = True
        a: Argument.Argument
        for a in self.AF_main.values():

            if not a.is_singleton:
                continue

            if len(a.defends) == 0:
                clause_right = z3.And(clause_right, z3.Implies(a.z3_value, True))
                continue

            clause_right_and = True

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF_main[b]

                if len(b.defends) == 0:
                    clause_right_and = False
                    break

                clause_right_or = False
                # get c: (c,b)∈R
                c: Argument.Argument
                for c in b.defends:
                    c = self.AF_main[c]
                    clause_right_or = z3.Or(clause_right_or, c.z3_value)
                clause_right_and = z3.And(clause_right_and, clause_right_or)

            clause_right = z3.And(clause_right, z3.Implies(a.z3_value, clause_right_and))

        clause = z3.And(clause_cf, clause_right)
        self.solver.add(z3.Not(clause))



    def computeSets(self, solution_amount: int=-1, algorithm: str="BFS"):
        return SemanticHelper.computeSets(self, solution_amount, algorithm)


    def verifySet(self, verify_set: list):
        return SemanticHelper.verifySet(self, verify_set)