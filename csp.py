import copy
import time
import itertools

class CSP:

    def __init__(self):
        # List of the variable names in the CSP
        self.variables = []

        # self.domains[i] is a list of legal values for variable i
        self.domains = {}

        # self.constraints[i][j] is a list of legal value pairs for
        # the variable pair (i, j)
        self.constraints = {}


    def add_variable(self, name, domain):
        """
        Adds a new variable to the CSP. name is the variable name
        and domain is a list of the legal values for the variable.
        """
        self.variables.append(name)
        self.domains[name] = list(domain)
        self.constraints[name] = {}


    def get_all_possible_pairs(self, a, b):
        """
        Get a list of all possible pairs (as tuples) of the values in
        the lists a and b, where the first component comes from list
        a and the second component comes from list b.
        """
        return itertools.product(a, b)


    def get_all_arcs(self):
        """
        Get a list of all arcs/constraints that have been defined in
        the CSP. The arcs/constraints are represented as tuples (i, j),
        indicating a constraint between variable i and j.
        """
        return [(i, j) for i in self.constraints for j in self.constraints[i]]


    def get_all_neighboring_arcs(self, var):
        """
        Get a list of all arcs/constraints going to/from variable. The 
        arcs/constraints are represented as in get_all_arcs().
        """
        return [(i, var) for i in self.constraints[var]]


    def add_constraint_one_way(self, i, j, filter_function):
        """
        Add a new constraint between variables i and j. The legal
        values are specified by supplying the filter_function
        that returns True for legal value pairs and False for illegal
        value pairs. This function only adds the constraint one way,
        from i -> j.
        """
        if not j in self.constraints[i]:
            # First, get a list of all possible pairs of values between variables i and j
            self.constraints[i][j] = self.get_all_possible_pairs(self.domains[i], self.domains[j])

        # Filter such that only legal values remain
        self.constraints[i][j] = list(filter(lambda value_pair: filter_function(*value_pair), self.constraints[i][j]))


    def add_all_different_constraint(self, variables):
        """
        Add an Alldiff constraint between all of the variables.
        """
        for (i, j) in self.get_all_possible_pairs(variables, variables):
            if i != j:
                self.add_constraint_one_way(i, j, lambda x, y: x != y)


    def backtracking_search(self):
        """
        Starts the CSP solver and returns the found solution.
        """
        global count_backtrack
        count_backtrack = 0
        global count_failures
        count_failures = 0

        # Make a deep copy of the dictionary containing the
        # domains of the CSP variables. The deep copy is required to
        # ensure that any changes made to assignment does not have any
        # side effects elsewhere.
        assignment = copy.deepcopy(self.domains)

        # Run AC-3 on all constraints in the CSP, to weed out all of the
        # values that are not arc consistent to begin with.
        self.inference(assignment, self.get_all_arcs())
        
        return self.backtrack(assignment)


    def backtrack(self, assignment):
        """Backtrack algorithm.

        The function is called recursively, with a partial assignment of
        values in assignment. assignment is a dictionary that contains
        a list of all legal values for the variables that have not yet
        been decided, and a list of only a single value for the
        variables that have been decided.

        When all of the variables in assignment have lists of length
        one, i.e. when all variables have been assigned a value, the
        function should return assignment. Otherwise, the search continues. 
        When the function inference is called to run the AC-3 algorithm, 
        the lists of legal values in assignment is reduced as AC-3 
        discovers illegal values.
        """
        global count_backtrack
        count_backtrack = count_backtrack + 1

        # Check to see if all variables have been assigned a value
        finished = True
        for variable,values in assignment.items():
            if len(values) != 1:
                finished = False
                break

        # Returning the assignment if its complete, i.e. all variables
        # have been assigned a single value
        if finished:
            return assignment

        variable = self.select_unassigned_variable(assignment)
        values = assignment[variable]

        for value in values:
          
            # Check to see if the value is consistent with the partial assignment
            consistent = True
            for otherVariable in assignment:
                if otherVariable != variable:
                    if otherVariable in self.constraints[variable]:
                        consistent = False
                        all_pairs = self.get_all_possible_pairs([value],assignment[otherVariable])
                        
                        for pair in all_pairs:
                            if pair in self.constraints[variable][otherVariable]:
                                consistent = True
                                break
                    
                    if not consistent:   
                        break
            
            if consistent:
                
                # Because all CSPs are commutative, its enough to set the value of 
                # only one single variable in each iteration
                assignment[variable] = [value]
                assignmentCopy = copy.deepcopy(assignment)
                inferences = self.inference(assignmentCopy, self.get_all_arcs())

                # Recursive call if the assignment is consistent
                if inferences:
                    result = self.backtrack(assignmentCopy)

                    # Complete and consistent assignment, i.e. a solution 
                    if result:
                        return result

            assignment[variable].remove(value)

        global count_failures
        count_failures = count_failures + 1

        return False  
        

    def select_unassigned_variable(self, assignment):
        """
        Returns one of the variables the assignment that have not yet been decided, i.e. whose list
        of legal values has a length greater than one.
        """
        for variable, values in assignment.items():
            if len(values) > 1:
                return variable


    def inference(self, assignment, queue):
        """AC-3 algorithm.

        Achieves binary arc consistency for every variable.
        """
        
        while queue: # Queue of arcs 
            (i, j) = queue.pop(0) # Remove first

            if self.revise(assignment, i, j):

                # If there is no possible assignment for variable i
                if len(assignment[i]) == 0:
                    return False
        
                # Add arcs to adjacent nodes to queue, excluding variable j
                neighboring_arcs = self.get_all_neighboring_arcs(i)
                for k in neighboring_arcs:
                    if k[0] != j:
                        queue.append(k)
 
        return True

            
    def revise(self, assignment, i, j):
        """
        assignment is the current partial assignment, that contains
        the lists of legal values for each undecided variable. i and
        j specifies the arc that should be visited. If a value is
        found in variable i's domain that doesn't satisfy the constraint
        between i and j, the value is deleted from i's list of
        legal values in assignment.
        """
        revised = False

        for x in assignment[i]:

            # If no value y in the domain of j allows (x,y) to satisfy the 
            # constraint between i and j, x is deleted from i's assignment list
            satisfied = False
            for y in assignment[j]:

                if (x,y) in self.constraints[i][j]:
                    satisfied = True
                    break

            # Returns True if revised such that the inference function can
            # propagate the changes done in the assignment         
            if not satisfied:
                assignment[i].remove(x)
                revised = True
        
        return revised


def create_map_coloring_csp():
    """
    Instantiate a CSP representing the map coloring problem of Australian states. 
    """
    csp = CSP()
    states = ['WA', 'NT', 'Q', 'NSW', 'V', 'SA', 'T']
    edges = {'SA': ['WA', 'NT', 'Q', 'NSW', 'V'], 'NT': ['WA', 'Q'], 'NSW': ['Q', 'V']}
    colors = ['red', 'green', 'blue']
    for state in states:
        csp.add_variable(state, colors)
    for state, other_states in edges.items():
        for other_state in other_states:
            csp.add_constraint_one_way(state, other_state, lambda i, j: i != j)
            csp.add_constraint_one_way(other_state, state, lambda i, j: i != j)
    return csp


def create_sudoku_csp(filename):
    """
    Instantiate a CSP representing the Sudoku board found in the
    current directory.
    """
    csp = CSP()
    board = list(map(lambda x: x.strip(), open(filename, 'r')))

    for row in range(9):
        for col in range(9):
            if board[row][col] == '0':
                csp.add_variable('%d-%d' % (row, col), list(map(str, range(1, 10))))
            else:
                csp.add_variable('%d-%d' % (row, col), [board[row][col]])

    for row in range(9):
        csp.add_all_different_constraint(['%d-%d' % (row, col) for col in range(9)])
    for col in range(9):
        csp.add_all_different_constraint(['%d-%d' % (row, col) for row in range(9)])
    for box_row in range(3):
        for box_col in range(3):
            cells = []
            for row in range(box_row * 3, (box_row + 1) * 3):
                for col in range(box_col * 3, (box_col + 1) * 3):
                    cells.append('%d-%d' % (row, col))
            csp.add_all_different_constraint(cells)

    return csp


def print_sudoku_solution(solution):
    """
    Convert the representation of a Sudoku solution as returned from
    the method CSP.backtracking_search(), into a human readable
    representation.
    """

    for row in range(9):
        for col in range(9):
            print(" " + solution['%d-%d' % (row, col)][0], end=" "),
            if col == 2 or col == 5:
                print('|',end=""),
        print("")
        if row == 2 or row == 5:
            print('---------+---------+---------')



csp = create_sudoku_csp('veryhard.txt')
startTime = time.time()
print_sudoku_solution(csp.backtracking_search())
endTime = time.time()
print("")
print(f"Runtime: {round(endTime-startTime,2)} seconds")
print(f"Number of backtrack calls: {count_backtrack}")
print(f"Number of failures: {count_failures}")




