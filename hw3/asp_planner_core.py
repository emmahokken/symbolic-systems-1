''' Emma Hokken - 10572090 '''

from planning import PlanningProblem, Action, Expr, expr
import planning

import clingo

def solve_planning_problem_using_ASP(planning_problem,t_max):
    """
    If there is a plan of length at most t_max that achieves the goals of a given planning problem,
    starting from the initial state in the planning problem, returns such a plan of minimal length.
    If no such plan exists of length at most t_max, returns None.

    Finding a shortest plan is done by encoding the problem into ASP, calling clingo to find an
    optimized answer set of the constructed logic program, and extracting a shortest plan from this
    optimized answer set.

    NOTE: still needs to be implemented. Currently returns None for every input.

    Parameters:
        planning_problem (PlanningProblem): Planning problem for which a shortest plan is to be found.
        t_max (int): The upper bound on the length of plans to consider.

    Returns:
        (list(Expr)): A list of expressions (each of which specifies a ground action) that composes
        a shortest plan for planning_problem (if some plan of length at most t_max exists),
        and None otherwise.
    """
    # initiate the code for the asp solver
    asp_code = ''

    # declare constant and time variables
    asp_code += f'#const tmax={t_max - 1}. time(0..tmax). '

    # add the initial states as facts to the program
    for state in planning_problem.initial:
        asp_code += f'state({str(state).swapcase()}, 0). '

    # encode effects of acitons
    for action in planning_problem.actions:
        # gather preconditions in the form of states at a certain timestep Z
        preconds = ''.join([f'state({str(precond).swapcase()}, Z), ' if '~' not in str(precond) else
                            f'-state({str(precond)[1:].swapcase()}, Z), ' for precond in action.precond])

        # create availability of actions, with precondition if these exist
        availability = f'available({str(action).swapcase()}, Z) :- {preconds}time(Z). '

        # add available actions to asp code
        asp_code += availability

    # ensure only one action is chosen at a time
    asp_code += '1 { chosen(A, Z) : available(A, Z) } 1 :- time(Z). '

    # ensure state is kept when moving to next timestep
    asp_code += 'state(P, Z+1) :- not -state(P, Z+1), state(P, Z), time(Z).'
    asp_code += '-state(P, Z+1) :- not state(P, Z+1), -state(P, Z), time(Z).'

    # encode effects of actions
    for action in planning_problem.actions:
        # create a new state for each effect
        for effect in action.effect:
            # create negative state if a negation is present and positive otherwise
            if '~' in str(effect):
                new_state = f'-state({str(effect)[1:].swapcase()}, Z+1) :- chosen({str(action).swapcase()}, Z), time(Z). '
            else:
                new_state = f'state({str(effect).swapcase()}, Z+1) :- chosen({str(action).swapcase()}, Z), time(Z). '
            asp_code += new_state

    # encode goals as states
    goals = ''.join([f'state({str(goal).swapcase()}, Z), ' if '~' not in str(goal) else
                    f'-state({str(goal)[1:].swapcase()}, Z), ' for goal in planning_problem.goals])

    # goals are met if all subsequent goals tates are satisfied
    asp_code += f'goal_met(Z) :- {goals} time(Z).'

    # once goals are met, ensure that this is remembered in the next timestep
    asp_code += 'goal_met(Z+1) :- goal_met(Z), time(Z).'

    # ensure goal is met before t_max
    asp_code += ':- not goal_met(tmax).'

    # ensure sum of Z for goal_met is maximised
    asp_code += '#maximize { Z : goal_met(Z) }.'

    # only return relevant variables
    asp_code += '#show chosen/2.'
    asp_code += '#show goal_met/1.'

    # solve model
    mod = solve(asp_code)

    # if no model was found, return None
    if not mod:
        return None

    # separate goals met and chosen variables in model
    goals_met = [a for a in mod  if 'goal_met' in a]
    chosens = [a for a in mod if 'chosen' in a]

    # retrieve timesteps from goals_met and sort the result
    goals_met_min = []
    for goal in goals_met:
        _, t = goal.split('(')
        goals_met_min.append(t[:-1])
    goals_met_min.sort(key=int)

    # sort chosen actions by the time they were chosen
    chosens.sort(key= lambda x:x[-2])
    chosens.sort(key= lambda x:x[-3:-2])

    # iterate over chosen actions, up to the first time the goal was met
    plan = []
    for i, choice in enumerate(chosens[:int(goals_met_min[0])]):
        # separate action from variable
        _, action = choice.split('chosen(')
        action, _ = action.split(f',{i}')
        # swap upper- and lowercase to retrieve original action format
        plan.append(expr(action.swapcase()))

    return plan

def solve(program):
    mod = []
    # load the answer set program, and call the grounder
    control = clingo.Control()
    control.add("base", [], program)
    control.ground([("base", [])])
    # define a function that will be called when an answer set is found
    # this function sorts the answer set alphabetically, and prints it
    def on_model(model):
        # ensure optimal model is found
        if model.optimality_proven == True:
            sorted_model = [str(atom) for atom in model.symbols(shown=True)]
            sorted_model.sort()
            mod.append(sorted_model)

    # ask clingo to find one model
    control.configuration.solve.opt_mode = "optN"
    control.configuration.solve.models = 1
    # call the clingo solver, passing on the function on_model for when an answer set is found
    answer = control.solve(on_model=on_model)
    # Print a message when no answer set was found
    if answer.satisfiable == False:
        return None
    else:
        return mod[0]
