:- initialization main.

parse(TokenList, AST) :- phrase(program(AST), TokenList).
/* Keyword Declarations */
reserved([var, return, function]).          % reserved words
operators(['<-', '.', ';', '(', ')', '{', '}']). % assign, statement terminator, parentheses
mathOp(['+', '-', '*', '/']).     % mathOp
logOp(['&&', '||']).              % logOp 
comparators(['==', '<', '>', '<=', '>=', '!=']).   % comparators
condWords(['if', 'else', 'then', 'endif']).     % conditions
loopWords(['while', 'do', 'done']).    % loop

/* Program recursive definition */
program(prog(retStatement(VALUE))) --> [return], base(VALUE), ['.'].  % terminating statement
program(prog(STATEMENT, PROGRAM)) --> statement(STATEMENT), [';'], program(PROGRAM).

statement(declaration(NAME)) --> [var], identity(NAME).
statement(assignment(NAME, VALUE)) --> identity(NAME), ['<-'], base(VALUE).
statement(decAssignment(NAME, VALUE)) --> [var], identity(NAME), ['<-'], base(VALUE).

statement(funcDecl(FUNC_NAME, FUNC_ARGS, FUNC_PROGRAM)) --> 
              ['function'], identity(FUNC_NAME), ['('], identity(FUNC_ARGS), [')'],  
              ['{'], program(FUNC_PROGRAM), ['}'].                                  
statement(conditional(COND, IF_BRANCH)) --> 
              ['if'], ['('], condition(COND), [')'], ['then'], statementSeq(IF_BRANCH), ['endif'].
statement(conditional(COND, IF_BRANCH, ELSE_BRANCH)) --> 
              ['if'], ['('], condition(COND), [')'], ['then'], statementSeq(IF_BRANCH), 
                                                     ['else'], statementSeq(ELSE_BRANCH), ['endif'].
statement(loop(COND, LOOP_BODY)) --> ['while'], ['('], condition(COND), [')'], 
                                     ['do'], statementSeq(LOOP_BODY), ['done'].

statementSeq(sseq(STATEMENT)) --> statement(STATEMENT), ['.'].
statementSeq(sseq(STATEMENT, REMAINDERS)) --> statement(STATEMENT), [';'], statementSeq(REMAINDERS).

condition(singcond(OPR_A, COMP, OPR_B)) --> base(OPR_A), comparator(COMP), base(OPR_B).
condition(mulcond(COND_A, LOGIC_OP, COND_B)) --> ['('], condition(COND_A), logical(LOGIC_OP), condition(COND_B), [')'].

comparator(COMP_OP) --> [COMP_OP], { comparators(COMPARATORS), member(COMP_OP, COMPARATORS) }.
logical(LOGIC_OP) --> [LOGIC_OP], { logOp(LOGIC_OPERATORS), member(LOGIC_OP, LOGIC_OPERATORS) }. 

/* Element-wise rule definition */
base(NAME) --> identity(NAME) | numerics(NAME) | ['('], expression(NAME), [')'].
base(funcCall(FUNC_NAME, FUNC_ACTUAL)) --> identity(FUNC_NAME), ['('], base(FUNC_ACTUAL), [')'].  % func call
expression(EXP) --> term(EXP) | term(TERM), ['+'], left_assoc(EXP, TERM, addition) | term(TERM), ['-'], left_assoc(EXP, TERM, subtraction).

/* left_assoc for math compuation */
% for every computational operators, 
% the first rule is the terminal rule (not generating more non-terminal)
% while the second rule is the recursive rule
left_assoc(compute(addition,TERM_A,TERM_B), TERM_A, addition) --> term(TERM_B).
left_assoc(EXP, TERM_A, addition) --> term(TERM_B), ['+'], left_assoc(EXP, compute(addition, TERM_A, TERM_B), addition).
left_assoc(EXP, TERM_A, addition) --> term(TERM_B), ['-'], left_assoc(EXP, compute(addition, TERM_A, TERM_B), subtraction).

left_assoc(compute(subtraction,TERM_A,TERM_B), TERM_A, subtraction) --> term(TERM_B).
left_assoc(EXP, TERM_A, subtraction) --> term(TERM_B), ['-'], left_assoc(EXP, compute(subtraction, TERM_A, TERM_B), subtraction).
left_assoc(EXP, TERM_A, subtraction) --> term(TERM_B), ['+'], left_assoc(EXP, compute(subtraction, TERM_A, TERM_B), addition).
left_assoc(compute(multiplication,TERM_A,TERM_B), TERM_A, multiplication) --> factor(TERM_B).
left_assoc(EXP, TERM_A, multiplication) --> term(TERM_B), ['*'], left_assoc(EXP, compute(multiplication, TERM_A, TERM_B), multiplication).
left_assoc(EXP, TERM_A, multiplication) --> term(TERM_B), ['/'], left_assoc(EXP, compute(multiplication, TERM_A, TERM_B), division).
left_assoc(compute(division,TERM_A,TERM_B), TERM_A, division) --> factor(TERM_B).
left_assoc(EXP, TERM_A, division) --> term(TERM_B), ['/'], left_assoc(EXP, compute(division,TERM_A, TERM_B), division).
left_assoc(EXP, TERM_A, division) --> term(TERM_B), ['*'], left_assoc(EXP, compute(division,TERM_A, TERM_B), multiplication).

term(TERM) --> factor(TERM) | 
               factor(VALUE), ['*'], left_assoc(TERM, VALUE, multiplication) | 
               factor(VALUE), ['/'], left_assoc(TERM, VALUE, division).

factor(FACTOR) --> base(FACTOR).
identity(NAME) --> [NAME], { 
                             reserved(Keyword), \+ member(NAME, Keyword), 
                             operators(Operator), \+ member(NAME, Operator),
                             mathOp(MathOperator), \+ member(NAME, MathOperator),
                             logOp(LogicOperator), \+ member(NAME, LogicOperator),
                             comparators(Comparators), \+ member(NAME, Comparators),
                             condWords(CondWords), \+ member(NAME, CondWords),
                             loopWords(LoopWords), \+ member(NAME, LoopWords),
                             \+ number(NAME)
                           }.
numerics(VALUE) --> [VALUE], { integer(VALUE) | float(VALUE) }.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%          EVALUATION OF AST          %%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
evaluate(AST, Number) :- 
    empty_assoc(VARIABLES),  % initialize an empty association list for variables
    empty_assoc(FUNCTIONS),  % initialize an empty association list for functions
    validate(AST, Number, VARIABLES, _, FUNCTIONS, _).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% LOGIC COMPONENTS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% evaluate all comparative computations
eval_cond(singcond(OPR_A, COMP_OP, OPR_B), _, VAR, VAR, FUNC, FUNC) :- 
    COMP_OP == '>',
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    VAL_OPR_A > VAL_OPR_B.
eval_cond(singcond(OPR_A, COMP_OP, OPR_B), _, VAR, VAR, FUNC, FUNC) :- 
    COMP_OP == '>=',
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    VAL_OPR_A >= VAL_OPR_B.
eval_cond(singcond(OPR_A, COMP_OP, OPR_B), _, VAR, VAR, FUNC, FUNC) :- 
    COMP_OP == '<',
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    VAL_OPR_A < VAL_OPR_B.
eval_cond(singcond(OPR_A, COMP_OP, OPR_B), _, VAR, VAR, FUNC, FUNC) :- 
    COMP_OP == '<=',
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    VAL_OPR_A =< VAL_OPR_B.
eval_cond(singcond(OPR_A, COMP_OP, OPR_B), _, VAR, VAR, FUNC, FUNC) :- 
    COMP_OP == '==',
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    VAL_OPR_A == VAL_OPR_B.
eval_cond(singcond(OPR_A, COMP_OP, OPR_B), _, VAR, VAR, FUNC, FUNC) :- 
    COMP_OP == '!=',
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    VAL_OPR_A \== VAL_OPR_B.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% LOGIC COMPONENTS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% validate all logical computations
eval_cond(mulcond(COND_A, LOGIC_OP, COND_B), _, VAR, VAR, FUNC, FUNC):- 
    LOGIC_OP == '&&',
    ( eval_cond(COND_A, _, VAR, VAR, FUNC, FUNC), eval_cond(COND_B, _, VAR, VAR, FUNC, FUNC) ).
eval_cond(mulcond(COND_A, LOGIC_OP, COND_B), _, VAR, VAR, FUNC, FUNC):- 
    LOGIC_OP == '||', 
    ( eval_cond(COND_A, _, VAR, VAR, FUNC, FUNC); eval_cond(COND_B, _, VAR, VAR, FUNC, FUNC) ). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% BASE COMPONENTS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% validate an empty program or statement
validate([], _, VAR, VAR, FUNC, FUNC).
% validate a literal number as it is
validate(X, X, VAR, VAR, FUNC, FUNC) :- number(X).
% validate a declared variable
validate(X, OUTCOME, VAR, VAR, FUNC, FUNC) :- 
    get_assoc(X, VAR, OUTCOME), OUTCOME \== empty.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% ARITHMETIC COMPONENTS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% validate all arithmetic computations.
validate(compute(addition, OPR_A, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- 
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    OUTCOME is VAL_OPR_A + VAL_OPR_B.
validate(compute(subtraction, OPR_A, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- 
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    OUTCOME is VAL_OPR_A - VAL_OPR_B.
validate(compute(multiplication, OPR_A, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- 
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    OUTCOME is VAL_OPR_A * VAL_OPR_B.
validate(compute(division, OPR_A, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- 
    VAL_OPR_B \== 0, 
    VAL_OPR_B \== 0, 
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    OUTCOME is VAL_OPR_A / VAL_OPR_B.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% VARIABLE COMPONENTS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% validate the return statement
validate(retStatement(VALUE), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    validate(VALUE, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
% validate the declaration statement
validate(declaration(NAME), _, PRE_VAR, POST_VAR, PRE_FUNC, PRE_FUNC) :- 
    \+ get_assoc(NAME, PRE_VAR, _), 
    put_assoc(NAME, PRE_VAR, empty, POST_VAR).
% validate the assignment statement
validate(assignment(NAME, VALUE), _, PRE_VAR, POST_VAR, PRE_FUNC, PRE_FUNC) :- 
    get_assoc(NAME, PRE_VAR, _), 
    validate(VALUE, OUTCOME, PRE_VAR, _, PRE_FUNC, _), 
    put_assoc(NAME, PRE_VAR, OUTCOME, POST_VAR).
% validate the decAssignment 
validate(decAssignment(NAME, VALUE), _, PRE_VAR, POST_VAR, PRE_FUNC, PRE_FUNC) :- 
    \+ get_assoc(NAME, PRE_VAR, _), 
    validate(VALUE, OUTCOME, PRE_VAR, _, PRE_FUNC, _), 
    put_assoc(NAME, PRE_VAR, OUTCOME, POST_VAR).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CONDITIONAL COMPONENTS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% validate the conditional
% a) general case: if-part of enterable if-then-endif statement
validate(conditional(COND, IF_BRANCH), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    eval_cond(COND, _, PRE_VAR, PRE_VAR, PRE_FUNC, PRE_FUNC),
    validate(IF_BRANCH, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
% b) corner case: cope with non-enterable if-part of the if-then-endif statement
validate(prog(conditional(COND, _), PROGRAM), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    \+ eval_cond(COND, _, PRE_VAR, PRE_VAR, PRE_FUNC, PRE_FUNC),
    validate(PROGRAM, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
% c) general case: if-part of enterable if-then-else-endif statement
validate(conditional(COND, IF_BRANCH, _), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    eval_cond(COND, _, PRE_VAR, PRE_VAR, PRE_FUNC, PRE_FUNC),
    validate(IF_BRANCH, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
% d) general case: else-part of enterable if-then-else-endif statement
validate(conditional(COND, _, ELSE_BRANCH), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    \+ eval_cond(COND, _, PRE_VAR, PRE_VAR, PRE_FUNC, PRE_FUNC),
    validate(ELSE_BRANCH, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% LOOP COMPONENTS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% validate the loop
validate(prog(loop(COND, _), PROGRAM), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    \+ eval_cond(COND, _, PRE_VAR, PRE_VAR, PRE_FUNC, PRE_FUNC),
    validate(PROGRAM, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
validate(loop(COND, LOOP_BODY), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    eval_cond(COND, _, PRE_VAR, PRE_VAR, PRE_FUNC, PRE_FUNC),
    validate(LOOP_BODY, _, PRE_VAR, IME_VAR, PRE_FUNC, IME_FUNC), 
    eval_cond(COND, _, IME_VAR, IME_VAR, IME_FUNC, IME_FUNC),
    validate(loop(COND, LOOP_BODY), OUTCOME, IME_VAR, POST_VAR, IME_FUNC, POST_FUNC).
validate(loop(COND, LOOP_BODY), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    eval_cond(COND, _, PRE_VAR, PRE_VAR, PRE_FUNC, PRE_FUNC),
    validate(LOOP_BODY, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC), 
    \+ eval_cond(COND, _, POST_VAR, POST_VAR, POST_FUNC, POST_FUNC).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% FUNCTION COMPONENTS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% validate function def: we have an late binding mechanism to cope with functions
validate(funcDecl(FUNC_NAME, FUNC_ARG, FUNC_BODY), _, PRE_VAR, PRE_VAR, PRE_FUNC, POST_FUNC) :-
    \+ get_assoc(FUNC_NAME, PRE_FUNC, _),
    \+ get_assoc(FUNC_NAME, PRE_VAR, _),
    put_assoc(FUNC_NAME, PRE_FUNC, funcInfo(FUNC_ARG, FUNC_BODY), POST_FUNC).

% validate function call
validate(funcCall(FUNC_NAME, FUNC_ACTUAL), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :-
    get_assoc(FUNC_NAME, PRE_FUNC, funcInfo(FUNC_ARG, FUNC_BODY)),
    validate(FUNC_ACTUAL, ACTUAL, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC),
    empty_assoc(EMPTY_NAMESPACE),
    put_assoc(FUNC_ARG, PRE_VAR, ACTUAL, TEMP_NAMESPACE),
    validate(FUNC_BODY, OUTCOME, TEMP_NAMESPACE, _, PRE_FUNC, POST_FUNC).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% STATEMENT SEQUENCE COMPONENTS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% validate sseq
validate(sseq(STATEMENT), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    validate(STATEMENT, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
validate(sseq(STATEMENT, REMAINDERS), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    validate(STATEMENT, _, PRE_VAR, IME_VAR, PRE_FUNC, IME_FUNC), 
    validate(REMAINDERS, OUTCOME, IME_VAR, POST_VAR, IME_FUNC, POST_FUNC).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PROGRAM COMPONENTS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% validate the single prog node
validate(prog(PROGRAM), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    validate(PROGRAM, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
% validate the prog node recursively
validate(prog(PROGRAM, AST), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    validate(PROGRAM, _, PRE_VAR, VAR_C, PRE_FUNC, FUNC_C), 
    validate(AST, OUTCOME, VAR_C, POST_VAR, FUNC_C, POST_FUNC).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TESTING COMPONENTS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test(Name, Tokens, Expected) :- parse(Tokens, AST), evaluate(AST, X),  
                    ( X \== Expected, write('['), write(Name), write(']'), write(': Fail. Result: '), write(X), 
                      write(', Expected: '), writeln(Expected) ; 
                      parse(Tokens, AST), evaluate(AST, X), X == Expected, 
                      write('['), write(Name), write(']'), writeln(': Pass. ') ).

test_IF_THEN :-
    test('T1', ['var', 'x', ';', 'x', '<-', -1, ';', 'if', '(', 'x', '!=', 0, ')', 'then', 'x', '<-', 10, '.', 'endif', ';', 'return', 'x', '.'], 10),
    test('T2', ['var', 'x', ';', 'x', '<-', 1, ';', 'if', '(', 'x', '==', 0, ')', 'then', 'x', '<-', 10, '.', 'endif', ';', 'return', 'x', '.'], 1),
    true.

test_WHILE :-
    test('T_WHILE_1', ['var', 'x', '<-', -3, ';', 'while', '(', 'x', '<', 0, ')', 'do', 'x', '<-', '(','x', '+', 1,')', '.', 'done', ';', 'return', 'x', '.'], 0),
    test('T_WHILE_2', ['var', 'x', '<-', 3, ';', 'while', '(', 'x', '<', 0, ')', 'do', 'x', '<-', '(','x', '+', 1,')', '.', 'done', ';', 'return', 'x', '.'], 3),
    test('T_WHILE_3', ['var', 'x', '<-', -1000, ';', 'while', '(', 'x', '!=', 0, ')', 'do', 'x', '<-', '(','x', '+', 1,')', '.', 'done', ';', 'return', 'x', '.'], 0),
    test('T_WHILE_4', ['var', 'x', '<-', 1000, ';', 'while', '(', 'x', '!=', 0, ')', 'do', 'x', '<-', '(','x', '-', 1,')', '.', 'done', ';', 'return', 'x', '.'], 0),
    test('T_WHILE_5', ['var', 'x', '<-', 0, ';', 'while', '(', 'x', '==', 0, ')', 'do', 'x', '<-', '(','x', '-', 1,')', '.', 'done', ';', 'return', 'x', '.'], -1),
    test('T_WHILE_6', ['var', 'x', '<-', -3, ';', 'while', '(', 'x', '<=', 0, ')', 'do', 'x', '<-', '(','x', '+', 1,')', '.', 'done', ';', 'return', 'x', '.'], 1),
    test('T_WHILE_7', ['var', 'x', '<-', -500, ';', 'while', '(', 'x', '<=', 10, ')', 'do', 'x', '<-', '(','x', '+', 1,')', '.', 'done', ';', 'return', 'x', '.'], 11),
    test('T_WHILE_11', ['var', 'x', '<-', 0, ';', 'while', '(', '(', 'x', '<=', 50, '&&', 'x', '<', 100, ')',')', 'do', 'x', '<-', '(','x', '+', 1,')', '.', 'done', ';', 'return', 'x', '.'], 51),
    test('T_WHILE_12', ['var', 'x', '<-', 0, ';', 'while', '(', '(', 'x', '<=', 50, '||', 'x', '<', 100, ')',')', 'do', 'x', '<-', '(','x', '+', 1,')', '.', 'done', ';', 'return', 'x', '.'], 100),
    test('T_WHILE_20', ['var', 'x', '<-', 0, ';', 'while', '(', '(', '(', 'x', '<=', 50, '&&', 'x', '<', 25, ')', '||', 'x', '<', 100, ')',')', 'do', 'x', '<-', '(','x', '+', 1,')', '.', 'done', ';', 'return', 'x', '.'], 100),
    test('T_WHILE_21', ['var', 'x', '<-', 0, ';', 'while', '(', '(', 'x', '<=', 500, '&&', '(', '(', 'x', '<', 125, '||', 'x', '<', 25, ')', '||', 'x', '<', 100, ')', ')',')', 'do', 'x', '<-', '(','x', '+', 1,')', '.', 'done', ';', 'return', 'x', '.'], 125),
    test('T_WHILE_22', ['var', 'x', '<-', 0, ';', 'while', '(', '(', 'x', '<=', 500, '||', '(', '(', 'x', '<', 125, '||', 'x', '<', 25, ')', '||', 'x', '<', 100, ')', ')',')', 'do', 'x', '<-', '(','x', '+', 1,')', '.', 'done', ';', 'return', 'x', '.'], 501),
    true.

test_FUNCTION :- 
    parse(['function', 'f', '(', 'x', ')', '{', 'return', 'x', '.', '}', ';', 'return', 'f', '(', '(', 10, '+', 1, ')', ')', '.'], AST), writeln(AST),
    true.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% MAIN: ENTRY POINT 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

main :- 
    test_IF_THEN,
    test_WHILE,
    test_FUNCTION,
    true.
