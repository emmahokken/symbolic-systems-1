''' Symbolic Systems 1 - Homework assignment 1
    Emma Hokken - 10572090 '''

# SAT packages
from pysat.formula import CNF
from pysat.solvers import MinisatGH

# CSP packages
from ortools.sat.python import cp_model

# ASP packages
import clingo

# ILP packages
import gurobipy as gp
from gurobipy import GRB

###
### Propagation function to be used in the recursive sudoku solver
###
def propagate(sudoku_possible_values,k):
    '''
        Propagation function to be used in the recursive sudoku solver.
        Iterates over all rows and columns and determines whether an impossible
        value is currently present arround it. Similar to a human approach.

        Returns: the filtered sudoku_possible_values
    '''
    kk = k * k

    # iterate over rows and columns
    for i in range(kk):
        for j in range(kk):
            # check whether a value is determined for a specific cell
            if len(sudoku_possible_values[i][j]) == 1:
                val = sudoku_possible_values[i][j][0]

                # remove value from other cells in row or column if it is present
                for l in range(kk):
                    # check whether value occurs in same row
                    if l != i and val in sudoku_possible_values[l][j]:
                        sudoku_possible_values[l][j].remove(val)
                    # check whether value occurs in same column
                    if l != j and val in sudoku_possible_values[i][l]:
                        sudoku_possible_values[i][l].remove(val)

                # determine block indices
                block_i = i - i % k
                block_j = j - j % k
                # iterate over blocks
                for l in range(block_i, block_i + k):
                    for m in range(block_j, block_j + k):
                        # look at other cells in block and remove value if present
                        if i != l and j != m and val in sudoku_possible_values[l][m]:
                            sudoku_possible_values[l][m].remove(val)

    return sudoku_possible_values

###
### Solver that uses SAT encoding
###
def solve_sudoku_SAT(sudoku,k):
    '''
        Function that solves a sudoku using a SAT solver.
        Creates the formula and feeds it to the MinisatGH solver.

        Returns: the filled in sudoku if it was solved, None otherwise.
    '''
    kk = k * k
    formula = CNF()

    # functions to be used within this solver
    def var_number(i, j, n):
        ''' Determines a unique index for a sudoku cell based in its row, column and possible value. '''
        return i*kk*kk + j*kk + n

    # create literals for values that are already filled in, these must always be satisfied
    for i in range(kk):
        for j in range(kk):
            if sudoku[i][j] != 0:
                clause = [var_number(i, j, sudoku[i][j])]
                formula.append(clause)

    # ensure all cells have at least one of the specified values
    for i in range(kk):
        for j in range(kk):
            clause = []
            # iterate over all possible values, determine the unique index
            for n in range(1, kk + 1):
                clause.append(var_number(i, j, n))
            # ensure at least one is satisfied
            formula.append(clause)

    # iterate over rows (needed for multiple checks)
    for i in range(kk):
        for j in range(kk):
            # ensure at most one value is picked
            for n1 in range(1, kk + 1):
                for n2 in range(n1+1, kk+1):
                    # only one of the two values can be true
                    clause = [-1*var_number(i, j, n1), -1*var_number(i, j, n2)]
                    formula.append(clause)

        # ensure proper row and column (no double values)
        for n in range(1, kk+1):
            for j1 in range(kk):
                for j2 in range(j1+1, kk):
                    # ensure no column contains same value twice
                    clause = [-1*var_number(i, j1, n), -1*var_number(i, j2, n)]
                    formula.append(clause)
                    # ensure no row contains same value twice
                    clause = [-1*var_number(j1, i, n), -1*var_number(j2, i, n)]
                    formula.append(clause)

    # create list with indices of blocks
    indices = create_indices(k)

    # iterate over block indices
    for ind in indices:
        # iterate over possible values
        for n in range(1, kk+1):
            # create every combination of block indices possible
            for i1 in range(len(ind)):
                for i2 in range(i1+1, len(ind)):
                    # ensure no value appears more than once
                    clause = [-1*var_number(ind[i1][0], ind[i1][1], n), -1*var_number(ind[i2][0], ind[i2][1], n)]
                    formula.append(clause)

    # initialise the solver and give it the formula
    solver = MinisatGH();
    solver.append_formula(formula);

    # attempt to solve formula
    answer = solver.solve();

    # fill the sudoku when an answer has been found
    if answer:
        # get model from solver
        model = solver.get_model()
        for i in range(kk):
            for j in range(kk):
                for n in range(1, kk+1):
                    if var_number(i, j, n) in model:
                        sudoku[i][j] = n
        return sudoku

    # return None when no solution was found
    return None

###
### Solver that uses CSP encoding
###
def solve_sudoku_CSP(sudoku,k):
    '''
        Function that solves a sudoku using a CSP solver.
        Creates variables for each cell with a range 1 to (k * k) and adds
        sudoku constraints on these variables.

        Returns: the filled in sudoku if it was solved, None otherwise.
    '''
    kk = k * k
    model = cp_model.CpModel();

    # create a variable for each square in the sudoku
    vars = {}
    for i in range(kk):
        for j in range(kk):
            # save variable with key 'i,j' in dictionary, specifying range from 1 to k*k
            vars[f"{i},{j}"] = model.NewIntVar(1, kk, f"x{i},{j}");

    # create conditions for variables already present in the sudoku
    for i in range(kk):
        for j in range(kk):
            if sudoku[i][j] != 0:
                model.Add(vars[f'{i},{j}'] == sudoku[i][j])

    # ensure no value appears twice in rows and columns
    for i in range(kk):
        for j1 in range(kk):
            for j2 in range(j1 + 1, kk):
                # ensure this constraint for columns
                model.Add(vars[f'{i},{j1}'] != vars[f'{i},{j2}'])
                # ensure this constraint for rows
                model.Add(vars[f'{j1},{i}'] != vars[f'{j2},{i}'])

    # create list with indices of blocks
    indices = create_indices(k)

    # iterate over given block indices
    for ind in indices:
        # create every possible combination of block indices
        for i1 in range(len(ind)):
            for i2 in range(i1 + 1, len(ind)):
                # ensure values are different in these cells
                model.Add(vars[f'{ind[i1][0]},{ind[i1][1]}'] != vars[f'{ind[i2][0]},{ind[i2][1]}'])

    # solve the created model
    solver = cp_model.CpSolver();
    answer = solver.Solve(model);

    # fill in sudoku when an answer has been found
    if answer == cp_model.FEASIBLE:
        for i in range(kk):
            for j in range(kk):
                sudoku[i][j] = solver.Value(vars[f'{i},{j}'])

        return sudoku

    # return None when no solution was found
    return None

###
### Solver that uses ASP encoding
###
def solve_sudoku_ASP(sudoku,k):
    '''
        Function that solves a sudoku using a ASP solver.
        Creates variables and conditions that must not be deemed False.

        Returns: the filled in sudoku if it was solved, None otherwise.
    '''
    kk = k * k

    # empty string that will hold asp code
    asp_code = ''

    # add constants and ranged values for row, col, and n (numbers in sudoku)
    asp_code += f'#const k={k}. #const kk={kk}. #const ind={kk-1}.'
    asp_code += 'row(0..ind). col(0..ind). n(1..kk).'

    # fill in cells already present in input sudoku
    for i in range(kk):
        for j in range(kk):
            if sudoku[i][j] != 0:
                asp_code += f'cell({i}, {j}, {sudoku[i][j]}).'

    # ensure only one value is filled in in cell
    asp_code += '1 { cell(I, J, V) : n(V) } 1 :- row(I), col(J).'

    # idea for rows and columns from Answer Set Solving in Practice book, chapter 3, but added value V
    # ensure no row and column are the same
    asp_code += ''' :- cell(I1, J, V), cell(I2, J, V), I1 != I2.
                    :- cell(I, J1, V), cell(I, J2, V), J1 != J2. '''

    # idea for block constraints taken from https://ddmler.github.io/asp/2018/07/10/answer-set-programming-sudoku-solver.html
    # ensure values in block are different from each other
    asp_code += ''' block(I, J, I2, J2) :- row(I), row(I2), col(J), col(J2), I/k == I2/k, J/k == J2/k.
                    :- cell(I, J, V), cell(I2, J2, V), block(I, J, I2, J2), I != I2, J != J2. '''

    # show only cell values
    asp_code += '#show cell/3.'

    # load answer set program and call grounder
    control = clingo.Control();
    control.add("base", [], asp_code);
    control.ground([("base", [])])

    def on_model(model):
        ''' Fill sudoku when a (valid) answer set is found. '''
        for atom in model.symbols(shown=True):
            content = [a.number for a in atom.arguments]
            sudoku[content[0]][content[1]] = content[2]

    # find all models and solve them
    control.configuration.solve.models = 1
    answer = control.solve(on_model=on_model)

    # if a valid answer was found, return filled sudoku
    if answer.satisfiable:
        return sudoku

    # return None when no solution was found
    return None

###
### Solver that uses ILP encoding
###
def solve_sudoku_ILP(sudoku,k):
    '''
        Function that solves a sudoku using a ILP solver.
        Initiates binary variables and creates constraints such that a sudoku
        can be solved.

        Returns: the filled in sudoku if it was solved, None otherwise.
    '''

    kk = k * k
    model = gp.Model()

    # create a variable for each square in the sudoku
    vars = {}
    for i in range(kk):
        for j in range(kk):
            for n in range(1, kk+1):
                # save (binary) variable with key 'i,j,n' in dictionary
                vars[f'{i},{j},{n}'] = model.addVar(vtype=GRB.BINARY, name=f"x({i},{j},{n})")

    # create conditions for variables already present in the sudoku
    for i in range(kk):
        for j in range(kk):
            if sudoku[i][j] != 0:
                model.addConstr(vars[f'{i},{j},{sudoku[i][j]}'] == 1)

    # ensure each cell has a value
    for i in range(kk):
        for j in range(kk):
            # gather all (k*k) variables that are possible in cell i,j in a list
            all_n = [vars[f'{i},{j},{n}'] for n in range(1, kk+1)]
            # ensure only one of those values is set to 1
            model.addConstr(gp.quicksum(all_n) == 1)

    # ensure proper value in cell for rows and columns
    for i in range(kk):
        for n in range(1, kk + 1):
            # save all values that can be present in each row, column
            col_values = [vars[f'{i},{j},{n}'] for j in range(kk)]
            row_values = [vars[f'{j},{i},{n}'] for j in range(kk)]
            # and ensure only one is set to true
            model.addConstr(gp.quicksum(col_values) == 1)
            model.addConstr(gp.quicksum(row_values) == 1)

    # create list with indices of blocks
    indices = create_indices(k)

    # iterate over generated block indices
    for block in indices:
        for n in range(1, kk+1):
            # ensure the sum of each value is exactly 1 in a block
            blocks = [vars[f'{i},{j},{n}'] for i,j in block]
            model.addConstr(gp.quicksum(blocks) == 1)

    # solve model
    model.optimize()

    # if an option was found, fill and return sudoku
    if model.status == GRB.OPTIMAL:
        for i in range(kk):
            for j in range(kk):
                for n in range(1, kk+1):
                    if vars[f'{i},{j},{n}'].x == 1:
                        sudoku[i][j] = n
        return sudoku

    # return None when no solution was found
    return None


def create_indices(k):
    ''' Creates indices of block in sudoku. '''

    kk = k * k
    indices = []
    # iterate over first and row and column in block
    for i in range(0, kk, k):
        for j in range(0, kk, k):
            # create list with block indices
            block = [(l, m) for l in range(i, i + k) for m in range(j, j + k)]
            indices.append(block)

    return indices
