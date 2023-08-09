import z3

# TODO: Define Solver correctly here. 
# TODO: Delete all previous clauses before usage
s = z3.Solver()



# -----------------------------------------------------------------------------
# Define clauses for admissible extensions
def setAdmissibleSet(all_nodes: list, z3_all_nodes: list, node_defends: dict):
    # get a: a∈A
    for a in all_nodes:

        # check if b exists
        if a not in node_defends:
            s.add(z3.Implies(z3_all_nodes[a], True))
            continue

        # (a -> ^{b:(b,a)∈R}(¬b)
        clause_left = True
        # (a -> ^{b:(b,a)∈R} (v{c:(c,b)∈R})))
        clause_right = True

        # get b: b:(b,a)∈R
        for b in node_defends[a]:
            clause_left = z3.And(clause_left, z3.Not(z3_all_nodes[str(b)]))
            
            # check if c exists
            if str(b) not in node_defends:
                clause_right = z3.And(clause_right, False)
                continue

            # get c: (c,b)∈R
            clause_right_right = False
            for c in node_defends[str(b)]:
                clause_right_right = z3.Or(clause_right_right, z3_all_nodes[str(c)])
                
            clause_right = z3.And(clause_right, clause_right_right)
        clause = z3.And(z3.Implies(z3_all_nodes[a], clause_left), z3.Implies(z3_all_nodes[a], clause_right))
        s.add(clause)