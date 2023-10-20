import z3

from utils import Argument
from utils import Solver
from utils import ClusterHelperFunctions
from utils import Info


class StableSolver:
    def __init__(self, AF: dict[str, Argument.Argument]) -> None:
        '''
        @AF ->        Argumentation Framework
        '''
        self.AF = AF
        self.solution = list()
        self.solver = z3.Solver()
        self.setRulesStable()



    # -----------------------------------------------------------------------------
    # Define clauses for admissible extensions
    def setRulesStable(self):
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
            clause_right = a.z3_value

            # get b: b:(b,a)∈R
            b: Argument.Argument
            for b in a.defends:
                b = self.AF[b]

                if b.is_singleton:
                    clause_left = z3.And(clause_left, z3.Not(z3.And(a.z3_value, b.z3_value)))
                    clause_right = z3.Or(clause_right, b.z3_value)

            clause = z3.And(clause_left, clause_right)
            self.solver.add(clause)
            print(clause)



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
            
        

    
    def verifySet(self, verify_set: list):
        if verify_set == [[]]:
            return True

        deconstructed_list = ClusterHelperFunctions.deconstructClusteredList(clustered_list=verify_set[0])

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
                    return verify_set

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
                    return verify_set

        return verify_set                