import z3

from utils import Argument
from . import SemanticHelper


class StableSolver:
    def __init__(self, AF: dict[str, Argument.Argument], AF_main: dict[str, Argument.Argument]) -> None:
        '''
        @AF ->        Argumentation Framework
        '''
        self.AF = AF
        self.AF_main = AF_main
        self.solution = list()
        self.solver = z3.Solver()
        self.setRulesStable()



    def setRulesStable(self):
        ''' Sets the rules for stable check. Formula is in the Readme'''
        
        cf_clause = True # conflict free part
        # get a: a∈A
        a: Argument.Argument
        for a in self.AF.values():

            if not a.is_singleton or len(a.defends) == 0:
                continue

            cf_clause_inner = True

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                if b.is_singleton:
                    cf_clause_inner = z3.And(cf_clause_inner, z3.Not(z3.And(a.z3_value, b.z3_value)))

            cf_clause = z3.And(cf_clause, cf_clause_inner)

        
        middle_clause = True # middle part of the formula
        # get a: a∈A
        a: Argument.Argument
        for a in self.AF.values():
            # check if b exists
            if len(a.defends) == 0:
                self.solver.add(z3.Or(a.z3_value, False))
                continue
            
            middle_clause_inner = False

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                middle_clause_inner = z3.Or(middle_clause_inner, b.z3_value)


            middle_clause = z3.And(middle_clause, z3.Or(a.z3_value, middle_clause_inner))

        
        right_clause = True # right part of the formula
        # get a: a∈A
        a: Argument.Argument
        for a in self.AF.values():

            # check if b exists
            if len(a.defends) == 0:
                self.solver.add(z3.Implies(z3.And(a.z3_value, True), True))
                continue

            right_clause_inner = True

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                right_clause_inner = z3.And(right_clause_inner, z3.Not(b.z3_value))

            
            right_right_clause = True
            # get c:(a, c)∈R
            c: Argument.Argument
            for c in a.attacks:
                c = self.AF[c]

                if not c.is_singleton:
                    continue

                right_right_clause = z3.And(right_right_clause, z3.Not(c.z3_value))

            right_clause = z3.And(right_clause, z3.Implies(z3.And(a.z3_value, right_clause_inner), right_right_clause))

        # Add the final clause to the solver 
        self.solver.add(z3.And(z3.And(cf_clause, middle_clause), right_clause))
        
        # skip empty set solution in calculation but add by hand
        clause = False
        for arg in self.AF.values():
            clause = z3.Or(clause, arg.z3_value)
        self.solver.add(clause)
    
        if self.AF_main == None:
            return
        
        #TODO: CHECK REFINEMENT
        return
        
        # Refinement
        # clause_left AND clause_cf AND clause_att AND clause_con

        #clause_left
        clause_left = True
        hat_a: Argument.Argument
        for hat_a in self.AF.values():
            
            if hat_a.is_singleton:
                continue

            clause_left_inner = False
            for a in hat_a.clustered_arguments:
                clause_left_inner = z3.Or(clause_left_inner, self.AF_main[a].z3_value) 

            clause_left = z3.Implies(hat_a.z3_value, clause_left_inner)


        #clause_cf
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
        

        #clause_att
        clause_att = False
        a: Argument.Argument
        for a in self.AF_main.values():

            # check if b exists
            if len(a.defends) == 0:
                clause_att = z3.Or(clause_att, z3.Not(a.z3_value))
                continue

            clause_att_inner = True
            
            # get b: b:(b,a)∈R
            b: Argument.Argument 
            for b in a.defends:
                b = self.AF_main[b]
                clause_att_inner = z3.And(clause_att_inner, z3.Not(b.z3_value))
            
            clause_att = z3.Or(z3.Not(a.z3_value), clause_att_inner)

        
        # clause_con
        clause_con = False
        a: Argument.Argument
        for a in self.AF_main.values():

            # check if b exists
            if len(a.defends) == 0:
                clause_con = z3.Or(clause_con, a.z3_value)
                continue

            clause_con_left = True
            # get b: b:(b,a)∈R
            b: Argument.Argument 
            for b in a.defends:
                b = self.AF_main[b]
                clause_con_left = z3.And(clause_con_left, z3.Not(b.z3_value))


            # check if c exists
            if len(a.attacks) == 0:
                continue


            clause_con_right = False
            # get c: b:(a,c)∈R
            c: Argument.Argument
            for c in a.attacks:
                c = self.AF_main[c]

                if not c.is_singleton:
                    continue

                clause_con_right = z3.Or(clause_con_right, c.z3_value)

            clause_con = z3.Or(clause_con, z3.And(clause_con_left, clause_con_right))

        self.solver.add(z3.And(z3.And(z3.And(clause_left, clause_cf), clause_att), clause_con))







    def computeSets(self, solution_amount: int=-1, algorithm: str="BFS"):
        return SemanticHelper.computeSets(self, solution_amount, algorithm)


    def verifySet(self, verify_set: list):
        return SemanticHelper.verifySet(self, verify_set)