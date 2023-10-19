import z3

from utils import Argument
from utils import Solver
from utils import ClusterHelperFunctions
from utils import Info


class AdmissibleSolver:
    def __init__(self, AF: dict[str, Argument.Argument]) -> None:
        '''
        @AF ->        Argumentation Framework
        @semantic  -> "conflict_free" or "admissible"
        @algorithm -> "BFS"=(Breadth First Search) or "DFS"=(Depth First Search)
        '''
        self.AF = AF
        self.solution = list()
        self.solver = z3.Solver()
        self.setRulesAdmissible()



    # -----------------------------------------------------------------------------
    # Define clauses for admissible extensions
    def setRulesAdmissible(self):
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
                    clause_left = z3.And(clause_left, z3.Not(z3.And(a.z3_value, b.z3_value)))

                clause_right_right = False
                # check if c exists
                if len(b.defends) == 0:
                    clause_right = z3.And(clause_right, False)
                    continue
                # get c: (c,b)∈R
                c: Argument.Argument
                for c in b.defends:
                    c = self.AF[c]
                    clause_right_right = z3.Or(clause_right_right, c.z3_value)
                    
                clause_right = z3.And(clause_right, clause_right_right)
            clause = z3.And(z3.Implies(a.z3_value, clause_left), z3.Implies(a.z3_value, clause_right))
            self.solver.add(clause)



    def computeSets(self, solution_amount: int=-1, algorithm: str="BFS"):
        ''' Computes the defined Sets with the according algorithm '''
        Info.info(f"Computing Admissible Sets with {algorithm}")

        if algorithm == "DFS":
            self.solution.clear()

        k = 0
        while ((model := Solver.solve(self.solver)) != False) and (len(self.solution) < solution_amount or solution_amount == -1):
            k += 1
            self.solution.append(Solver.transformModelIntoArguments(arguments=self.AF, model=model))
            self.solver.add(Solver.negatePreviousModel(arguments=self.AF, model=model))
        else:
            Info.info(f"Found {k} many solutions")
            if algorithm == "BFS":
                return self.solution
            else:
                if len(self.solution) < solution_amount:
                    return False
                return self.solution
            
        

    
    def verifySet(self, admissible_set: list):
        if admissible_set == [[]]:
            return True

        deconstructed_list = ClusterHelperFunctions.deconstructClusteredList(clustered_list=admissible_set[0])

        for combination in deconstructed_list: 
            if len(deconstructed_list) > 1:
                for solution in combination:
                    self.solver.push()
                    for arg in solution:
                        self.solver.add(self.AF[arg].z3_value == True)

                    if Solver.solve(self.solver):
                        self.solver.pop()
                        return True
                    else:
                        self.solver.pop()
                else:
                    return admissible_set

            else: 
                self.solver.push()
                for argument in self.AF.keys():
                    if argument in combination:
                        self.solver.add(self.AF[argument].z3_value == True)
                    else:
                        self.solver.add(self.AF[argument].z3_value == False)
                if Solver.solve(self.solver):
                    self.solver.pop()
                    return True
                else:
                    self.solver.pop()
                    return admissible_set

        return admissible_set                