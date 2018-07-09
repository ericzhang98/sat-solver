class Literal:
    def __init__(self, var, pol):
        self.var = var
        self.pol = pol

    def __eq__(self, other):
        return self.var == other.var and self.pol == other.pol

    def __hash__(self):
        return hash((self.var, self.pol))

class Clause:
    def __init__(self, literals):
        self.literals = frozenset(literals)

    def __eq__(self, other):
        return self.literals == other.literals

    def __hash__(self):
        return hash(self.literals)

def unit_prop(clauses, assignments, active_clauses, assignment_stack):
    did_assign = True
    # keep assigning until we iterate thru without finding a unit clause
    # print "og assignments:", assignments
    while did_assign:
        did_assign = False
        # print "iterating..."
        for clause in list(clauses):
            # naive sat/unit check
            num_unassigned = 0
            clause_satisfied = False
            unit = None
            for l in clause.literals:
                # unassigned var -> inc count
                if assignments[l.var] == None:
                    num_unassigned += 1
                    unit = l
                # assigned var -> true -> rm clause
                else:
                    if assignments[l.var] == l.pol:
                        clauses.remove(clause)
                        clause_satisfied = True
                        break
            
            # contradiction if all assigned and False
            if num_unassigned == 0 and not clause_satisfied:
                """
                print "---"
                print "contradiction in clause:"
                for l in clause.literals:
                    print l.pol, l.var
                print "---"
                """
                return False, clauses
            # only one unassigned var so clause is unit, assign that var
            if num_unassigned == 1 and not clause_satisfied:
                """
                print "---"
                print "unit clause:"
                for l in clause.literals:
                    print l.pol, l.var
                print "assigning %s to %d" % (unit.pol, unit.var)
                print "---"
                """
                assignments[unit.var] = unit.pol
                assignment_stack.append((unit.var, unit.pol))
                did_assign = True

    # no contradiction detected, so return True, updated clauses
    return True, clauses


# guess True on first unassigned var
def make_decision(clauses, assignments):
    for c in clauses:
        for l in c.literals:
            if assignments[l.var] == None:
                print "---"
                print "decision: %d -> %s" % (l.var, True)
                print "---"
                return l.var, True

    print "no decisions to make in make_decision..."

def dpll(clauses):
    # build map of var -> val
    assignments = {}
    for c in clauses:
        for literal in c.literals:
            assignments[literal.var] = None
    decision_stack = []
    assignment_stack = []
    clauses_stack = []
    print "Starting with %d clauses" % len(clauses)
    eliminate_pure_literals(clauses, assignments) # rm literals and add assignments
    print "Pure literal eliminates down to %d clauses" % len(clauses)
    # active_clauses = eliminate_singletons(clauses) # should always reflect updated clauses after assignments
    active_clauses = []
    print "Starting with %d initial active clauses" % len(clauses)
    print "---"

    while True:
        # prop prev decision
        success, updated_clauses = unit_prop(copy.copy(clauses), assignments, active_clauses, assignment_stack)
        clauses = updated_clauses
        print "Decision stack:", decision_stack
        print "Finished unit prop, success:", success

        # finished prop and implications of prev decision
        # if no issues, keep going
        if success:
            if all(assignments[k] != None for k in assignments) or len(clauses) == 0: #toopt
                for k in assignments:
                    if assignments[k] == None:
                        assignments[k] = "Anything"
                        #assignments[k] = True
                return True, assignments
            else:
                # new decision
                var, val = make_decision(clauses, assignments)
                assignments[var] = val
                decision_stack.append((var, val))
                assignment_stack.append((var, val))
                print "Make decision: %d -> %s" % (var, val)
                clauses_stack.append(clauses) # each clauses entry in stack will correspond to the clauses right before a decision and its unit prop is made

        else:
            # contradiction after a non-decision propagation (after first var chosen is assigned)
            if len(decision_stack) == 0:
                return False, assignments
            else:
                # undo prev decision and return back to the og clauses right before decision was made (before unit prop of decision)
                dec_var, dec_val = decision_stack.pop()
                clauses = clauses_stack.pop()

                # undo the implied vars from prev decision until prev decision tup is popped
                var, val = assignment_stack.pop()
                while (var, val) != (dec_var, dec_val):
                    assignments[var] = None
                    var, val = assignment_stack.pop()

                # put inverse of prev decision since it's forced
                assignments[dec_var] = not dec_val 
                assignment_stack.append((dec_var, not dec_val))
                print "---"
                print "forced assignment: %d -> %s" % (dec_var, not dec_val)
                print "---"

    
def eliminate_singletons(clauses):
    singletons = set()
    for clause in list(clauses):
        if len(clause.literals) == 1:
            clauses.remove(clause)
            singletons.add(clause)
    return singletons

# go thru list of clauses and rm/assign pure literals
# we only run at beginning since it's expensive
def eliminate_pure_literals(clauses, assignments):
    polarities = {}
    pure = {}
    for k in assignments:
        pure[k] = True

    for clause in clauses:
        for literal in clause.literals:
            if literal.var in polarities:
                if polarities[literal.var] != literal.pol:
                    pure[literal.var] = False
            else:
                polarities[literal.var] = literal.pol

    for k in pure:
        if pure[k]:
            print "Pure literal assignment: %d -> %s" % (k, polarities[k])
            assignments[k] = polarities[k]

    # rm clauses that have a confirmed sat assignment
    for clause in list(clauses):
        for literal in clause.literals:
            if literal.var in assignments:
                if assignments[literal.var] != None:
                    if assignments[literal.var] == literal.pol:
                        clauses.remove(clause)
                    else:
                        print "WEIRD ERROR, PURE LITERAL HAS A FALSE"


import sys
import math
import copy
import time
start = time.time()
fname = sys.argv[1]
with open(fname) as fin:
    content = fin.readlines()
    content = [x.strip() for x in content]

meta = content[0].split(' ')
num_vars = int(meta[2])
num_clauses = int(meta[3])

clauses = set()
for line in content[1:]:
    line_arr = line.split(' ')
    literals = set()
    for l in line_arr[:-1]:
        literal = Literal(abs(int(l)), int(l) > 0)
        literals.add(literal)

    clause = Clause(literals)
    """
    print "---"
    for l in clause.literals:
        print l.pol, l.var
    print "---"
    """
    clauses.add(clause)

res, assignments = dpll(clauses)

print "---"
print "DPLL RESULT:"
print res
print assignments

success = True
for c in clauses:
    if any(assignments[l.var] == l.pol for l in c.literals) != True:
        success = False
        break
print "Final success:", success


from subprocess import Popen, PIPE

def run_sat_solver(asdf='asdf.cnf'):
    p = Popen(['./picosat', asdf], stdin=PIPE, stdout=PIPE, stderr=PIPE)
    output, err = p.communicate(b"input data that is passed to subprocess' stdin")
    rc = p.returncode
    return output


def decode(sat_encoding):
    lines = sat_encoding.split("\n")
    res = {}
    for l in lines[1:]:
        info_arr = l[2:].split(" ")
        for var_str in info_arr:
            var_num = int(var_str)
            if var_num == 0:
                return res
            if var_num > 0:
                res[var_num] = True
            if var_num < 0:
                res[abs(var_num)] = False

sat_output = run_sat_solver(asdf=fname)
sat_output_assignments = decode(sat_output)
print "Matches picosat:", sat_output_assignments == assignments
print "Time:", time.time() - start
"""
for k in assignments:
    if assignments[k] != sat_output_assignments[k]:
        print k, assignments[k], sat_output_assignments[k]
"""
