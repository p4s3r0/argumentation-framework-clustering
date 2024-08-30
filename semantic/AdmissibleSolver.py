import z3

from utils import Argument
from . import SemanticHelper


class AdmissibleSolver:
    def __init__(self, AF: dict[str, Argument.Argument], AF_main: dict[str, Argument.Argument]) -> None:
        '''
        @AF ->        Argumentation Framework
        '''
        self.AF = AF
        self.AF_main = AF_main
        self.solution = list()
        self.solver = z3.Solver()
        self.setRulesAdmissible()



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

        #TODO: Check refinement
        return
        if self.AF_main == None:
            return
        
        # refinement addition
        # clause_left AND clause_cf AND clause_def

        clause_left = True
        hat_a: Argument.Argument
        for hat_a in self.AF.values():
            
            if hat_a.is_singleton:
                continue

            clause_left_inner = False
            for a in hat_a.clustered_arguments:
                clause_left_inner = z3.Or(clause_left_inner, self.AF_main[a].z3_value) 

            clause_left = z3.Implies(hat_a.z3_value, clause_left_inner)

        

        clause_cf = False
        a: Argument.Argument
        for a in self.AF_main.values():

            if not a.is_singleton:
                continue 

            # check if b exists
            if len(a.defends) == 0:
                continue

            clause_cf_inner = False
            
            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF_main[b]
                if not b.is_singleton:
                    continue
                
                clause_cf_inner = z3.Or(clause_cf_inner, z3.And(a.z3_value, b.z3_value))

            clause_cf = z3.Or(clause_cf, clause_cf_inner)



        clause_def = False
        a: Argument.Argument
        for a in self.AF_main.values():
            if not a.is_singleton:
                continue 
            
            # check if b exists
            if len(a.defends) == 0:
                clause_def = z3.Or(clause_def, z3.And(a.z3_value, False))
                continue

            clause_def_inner = False

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF_main[b]
                #check if c exists
                if len(b.defends) == 0:
                    continue

                clause_def_inner_right = True
                
                c: Argument.Argument
                for c in b.defends:
                    c = self.AF_main[c]
                    clause_def_inner_right = z3.And(clause_def_inner_right, z3.Not(c.z3_value))

                clause_def_inner = z3.Or(clause_def_inner, clause_def_inner_right)

            clause_def = z3.Or(clause_def, z3.And(a.z3_value, clause_def_inner))

        self.solver.add(z3.And(z3.And(clause_left, clause_cf), clause_def))



                
            



        





    def computeSets(self, solution_amount: int=-1, algorithm: str="BFS"):
        return SemanticHelper.computeSets(self, solution_amount, algorithm)


    def verifySet(self, verify_set: list):
        return SemanticHelper.verifySet(self, verify_set)