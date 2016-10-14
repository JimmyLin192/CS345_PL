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
    VAL_OPR_B \== 0.0, 
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
validate(funcDecl(FUNC_NAME, FUNC_ARG, FUNC_BODY), _, VARS, VARS, PRE_FUNC, POST_FUNC) :-
    \+ get_assoc(FUNC_NAME, PRE_FUNC, _),
    put_assoc(FUNC_NAME, PRE_FUNC, funcInfo(FUNC_ARG, FUNC_BODY), POST_FUNC).

% validate function call
validate(funcCall(FUNC_NAME, FUNC_ACTUAL), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :-
    get_assoc(FUNC_NAME, PRE_FUNC, funcInfo(FUNC_ARG, FUNC_BODY)),
    validate(FUNC_ACTUAL, ACTUAL, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC),
    empty_assoc(EMPTY_NAMESPACE),
    put_assoc(FUNC_ARG, EMPTY_NAMESPACE, ACTUAL, TEMP_NAMESPACE),
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
% Reference: https://docs.google.com/document/d/1skDFXKI4ZRn14-Al5T6zraJLV6xaqFfmx-6oUQXXmyA/edit

writeTestName(Name) :- write('['), write(Name), write(']').

test(Name, Tokens, Expected) :- 
    \+ parse(Tokens, _), 
    Expected == 'parse_fail', 
    ansi_format([bold, fg(cyan)], '[~w]: Pass - Parse Fail As Expected. \n', [Name]).

test(Name, Tokens, Expected) :- 
    parse(Tokens, AST), 
    \+ evaluate(AST, _),  
    ( Expected == 'eval_fail' | Expected == 'evaluate_fail'), 
        ansi_format([bold, fg(cyan)], '[~w]: Pass - Evaluate Fail As Expected. \n', [Name]).

test(Name, Tokens, Expected) :- 
    parse(Tokens, AST), evaluate(AST, X), (
        ( X \== Expected, 
            ansi_format([bold, fg(red)], '[~w]: Fail.', [Name]),
            write(' Result: '), write(X), 
            write(', Expected: '), writeln(Expected) )  
     |  ( X == Expected, 
        ansi_format([bold, fg(cyan)], '[~w]: Pass. \n', [Name])
        )).

test_PARSE_FAIL :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases that should fail at the parsing stage. '),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_PARSE_FAIL_1', ['function', 'f', '(', 'x', ',', 'y', ')', '{', 'return', 'x', '.', '}', ';', 'return', 'f', '(', 10 , ')', '.'], 'parse_fail'),
    test('T_PARSE_FAIL_2', ['var', 'function', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_3', ['var', 'if', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_4', ['var', 'then', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_5', ['var', 'else', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_6', ['var', 'endif', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_8', ['var', 'while', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_9', ['var', '<', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_10', ['var', '>', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_11', ['var', '<=', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_12', ['var', '>=', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_13', ['var', '==', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_14', ['var', '!=', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_15', ['var', '||', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_16', ['var', '&&', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_17', ['return', 3, '+', 5, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_18', ['var', 'x', ';', 'x', '<-', 3, '+', 5, ';', 'return', 10, '+', 5, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_19', ['var', 'x', '<-', 3, '+', 5, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_20', ['var', 'x', 'x', '<-', 3, '+', 5, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_21', ['var', 'x', ';', ';', '<-', 3, '+', 5, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_22', ['var', 'x', ';', 'x', '<-', '(', 3, '+', 5, ')', ';', 'return', 10], 'parse_fail'),
    test('T_PARSE_FAIL_23', ['var', 'x', ';', 'x', '<-', '(', 3, '+', 5, ')', ';', 'return', 10, '.', '.'], 'parse_fail'),
    test('T_PARSE_FAIL_24', ['var', 'x', ';', 'x', '<-', '(', 3, 'a', 5, ')', ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_25', ['var', 'x', ';', 'x', '<-', '(', 3, 5, ')', ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_26', ['var', 'x', ';', 'x', '<-', '(', 3, '+', '+', 5, ')', ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_27', ['var', 'x', ';', 3, ';', 'x', '<-', '(', 3, '+', 5, ')', ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_28', ['var', 8, ';', 'x', '<-', '(', 3, '+', 5, ')', ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_29', ['return', '.'], 'parse_fail'),
    test('T_PARSE_FAIL_30', ['return', ';', 'return', 1, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_31', ['a', '<-', '1', '.'], 'parse_fail'),
    test('T_PARSE_FAIL_32', ['var', 'a', ';', 'a', '<-', 1, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_33', ['var', 'a', ';', 'a', '<-', 1, ';', 'return', 'a', '.', 'a', '<-', 0], 'parse_fail'),
    test('T_PARSE_FAIL_34', ['var', 'a', ';', 'a', '<-', 1, ';', 'return', 'a', '.', 'a', '<-', 0, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_35', ['var', 'var', ';', 'var', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_36', ['var', 'return', ';', 'return', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_37', ['var', '+', ';', '+', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_38', ['var', '-', ';', '-', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_39', ['var', '*', ';', '*', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_40', ['var', '/', ';', '/', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_41', ['var', '.', ';', '.', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_42', ['var', ';', ';', ';', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_43', ['var', '(', ';', '(', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_44', ['var', ')', ';', ')', '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_45', ['var', 10, ';', 10, '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    test('T_PARSE_FAIL_46', ['var', 10.0, ';', 10.0, '<-', 100, ';', 'return', 10, '.'], 'parse_fail'),
    writeln('').

test_EVAL_FAIL :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases that should fail at evaluation stage. '),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_EVAL_FAIL_1', ['return', 'x', '.'], 'eval_fail'),
    test('T_EVAL_FAIL_2', ['return', 'f', '(', 10 , ')', '.'], 'eval_fail'),
    test('T_EVAL_FAIL_3', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '<=', 3, ')', 'then', 'out', '<-', 1, '.', 'endif', ';', 'return', 'out', '.'], 'eval_fail'),
    test('T_EVAL_FAIL_4', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '>=', 6, ')', 'then', 'out', '<-', 1, '.', 'endif', ';', 'return', 'out', '.'], 'eval_fail'),
    writeln('').

test_PAREN :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for PARENTHESES. '),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_PAREN_FAIL_1', [return,'(',1,'.'], 'parse_fail'),
    test('T_PAREN_FAIL_2', [return,1,')','.'], 'parse_fail'),
    test('T_PAREN_FAIL_3', [return,'(',42,'(',')',')','.'], 'parse_fail'),
    test('T_PAREN_1', [return,'(',42,')','.'], 42),
    test('T_PAREN_2', [return,'(','(',42,')',')','.'], 42),
    writeln('').

test_ARITHMETIC :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for ARITHMETIC'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_ARITHMETIC_0', ['return','(',1,+,1,')','.'], 2),
    test('T_ARITHMETIC_1', ['return','(',2,*,2,')','.'], 4),
    test('T_ARITHMETIC_2', ['return','(',1,+,1,+,1,')','.'], 3),
    test('T_ARITHMETIC_3', ['return','(',2,*,4,*,6,')','.'], 48),
    test('T_ARITHMETIC_4', ['return','(',1,-,1,')','.'], 0),
    test('T_ARITHMETIC_5', ['return','(',2,/,2,')','.'], 1),
    test('T_ARITHMETIC_6', ['return','(',1,-,1,+,1,')','.'], 1),
    test('T_ARITHMETIC_7', ['return','(',64,/,2,/,8,')','.'], 4),
    test('T_ARITHMETIC_8', ['return','(',1,+,'(',1,+,1,')',')','.'], 3),
    test('T_ARITHMETIC_9', ['return','(',2,*,'(',2,/,2,')',')','.'], 2),
    test('T_ARITHMETIC_10', ['return','(',4,-,'(',2,-,1,')',')','.'], 3),
    test('T_ARITHMETIC_11', ['return','(',4,/,'(',2,-,-2,')',')','.'], 1),
    test('T_ARITHMETIC_12', ['return','(',1,*,'(',3,/,2,')',')','.'], 1.5),
    test('T_ARITHMETIC_13', ['return','(',2.5,*,'(',3,/,2,')',')','.'], 3.75),
    test('T_ARITHMETIC_14', ['return','(',2.5,+,3.66,')','.'], 6.16),
    test('T_ARITHMETIC_15', ['return','(',2.5,-,1.01,')','.'], 1.49),
    test('T_ARITHMETIC_16', ['return','(',2.5,-,1.01,+,'(',3,*,1.5,')',')','.'], 5.99),
    test('T_ARITHMETIC_17', ['return','(',2,*,9,/,6,')','.'], 3),
    test('T_ARITHMETIC_31', ['return','(',1,-,1,+,1,+,10,')','.'], 11),
    test('T_ARITHMETIC_32', ['return','(',10,'-',1,'+',2,'*',10,')','.'],  29),
    test('T_ARITHMETIC_33', ['return','(',10,'-',10,'/',2,'+',10,')','.'], 15),
    test('T_ARITHMETIC_34', ['return','(',10,'-',10,'*',5,'-',10,')','.'], -50),
    test('T_ARITHMETIC_35', ['return','(',10,'+',10,'-',5,'-',10,')','.'], 5),
    test('T_ARITHMETIC_36', ['return','(',10,'+',10,'-',5,'+',10,')','.'], 25),
    test('T_ARITHMETIC_37', ['return','(',1,'+',10,'-',5,'+',10,'-',11,')','.'], 5),
    test('T_ARITHMETIC_38', ['return','(',1,'+',8,'+',5,'-',10,'+',9,')','.'],  13),
    test('T_ARITHMETIC_39', ['return','(',10,'*',8,'/',2,'/',10,')','.'],     4),
    test('T_ARITHMETIC_40', ['return','(',8,'*',10,'/',2,'*',10,')','.'],     400),
    test('T_ARITHMETIC_41', ['return','(',5,'/',10,'*',2,'*',210,')','.'],    210.0),
    test('T_ARITHMETIC_42', ['return','(',3,'/',4,'*',20,'*',2,')','.'], 30.0),
    test('T_ARITHMETIC_43', ['return','(',3,'/',4,'*',8,'+',2,')','.'],  8.0),
    test('T_ARITHMETIC_44', ['return','(',3,'/',4,'*',8,'-',2,')','.'],  4.0),
    test('T_ARITHMETIC_45', ['return','(',3,'*',4,'/',8,'+',1,')','.'],  2.5),
    test('T_ARITHMETIC_46', ['return','(',3,'*',40,'/',4,'*',10,'+',1,')','.'], 301),
    test('T_ARITHMETIC_51', ['return', '(', 64, '/', 2, '/', 8, ')', '.'], 4),
    test('T_ARITHMETIC_52', ['return', '(', 2.5, '-', 1.01, '+', '(', 3, '*', 1.5, ')', ')', '.'], 5.99),
    test('T_ARITHMETIC_53', ['var', 'x', '<-', '(', 3, '*', 2, '-', 4, ')', ';', 'var', 'y', '<-', '(', 5, '+', 6, '/', 2, ')', ';', 'var', 'z', '<-', '(', 3, '*', 4, '/', 2, ')', ';', 'return', '(', 'x', '-', 'y', '*', 'z', ')', '.'], -46),
    test('T_ARITHMETIC_54', ['var', 'x', '<-', '(', 3, '*', 2, '*', 4, ')', ';', 'var', 'y', '<-', '(', 5, '+', 6, '+', 2, ')', ';' , 'var', 'z', '<-', '(', 3, '-', 4, '-', 2, ')', ';', 'return', '(', 'x', '/', 'y', '/', 'z', ')', '.'], -0.6153846153846154),
    writeln('').

test_DECASSIGN :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for DECASSIGN'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_DECASSIGN_1', ['var', 'x', '<-', 1, ';', 'return', x, '.'], 1),
    test('T_DECASSIGN_2', ['var', 'x', '<-', 1, ';', 'x', '<-', 100, ';', 'return', 'x', '.'], 100),
    test('T_DECASSIGN_3', ['var', 'x', '<-', 1, ';', 'var', 'y', ';', 'y', '<-', 10, ';', 'return', '(', 'x', '+', 'y', ')', '.'], 11),
    test('T_DECASSIGN_4', ['var', 'x', '<-', 1, ';', 'var', 'y', ';', 'y', '<-', 1000, ';', 'x', '<-', 'y', ';', 'return', 'x', '.'], 1000),
    test('T_DECASSIGN_5', ['var', 'y', ';', 'y', '<-', 1000, ';', 'var', 'x', '<-', 'y', ';', 'return', 'x', '.'], 1000),
    test('T_DECASSIGN_6', ['var', 'x', '<-', '(', 10, '+', 5, ')', ';', 'return', x, '.'], 15),
    test('T_DECASSIGN_7', ['var', 'y', ';', 'y', '<-', 2, ';', 'var', 'x', '<-', '(', 10, '+', 'y', ')', ';', 'return', 'x', '.'], 12),
    test('T_DECASSIGN_8', ['var', 'x', '<-', 1.12355, ';', 'return', x, '.'], 1.12355),
    test('T_DECASSIGN_9', ['var', 'x', '<-', 1, ';', 'var', 'x', ';', 'return', 'x', '.'], 'eval_fail'),
    test('T_DECASSIGN_10', ['var', 'x', '<-', 1, ';', 'var', 'x', '<-', 4, ';', 'return', 'x', '.'], 'eval_fail'),
    test('T_DECASSIGN_11', ['var', 'x', '<-', 'a', ';', 'return', 10, '.'], 'eval_fail'),
    test('T_DECASSIGN_12', ['var', 'x', '<-', 'x', ';', 'return', 10, '.'], 'eval_fail'),
    test('T_DECASSIGN_13', ['var', 'x', ';', 'x', '<-', 2, ';', 'var', 'x', '<-', 10, ';', 'return', 10, '.'], 'eval_fail'),
    writeln('').

test_VARIABLE :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for VARIABLES'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_VARS_EFAIL_01', [return,x,.] ,'eval_fail'),
    test('T_VARS_EFAIL_02', [var,x,;,return,x,'.'] , 'eval_fail'),
    test('T_VARS_EFAIL_03', [x,<-,1,;,return,x,'.'], 'eval_fail'),
    test('T_VARS_EFAIL_04', [x,<-,1,;,return,1,'.'], 'eval_fail'),
    test('T_VARS_EFAIL_05', [var,x,;,var,y,;,x,<-,1,;,return,'(',x,+,y,')','.'], 'eval_fail'),
    test('T_VARS_EFAIL_06', [var,x,;,var,y,;,x,<-,a,;,y,<-,1000,;,x,<-,y,;,return,x,'.'], 'eval_fail'),
    test('T_VARS_EFAIL_07', [var,x,;,var,y,;,x,<-,1,;,y,<-,a,;,x,<-,y,;,return,y,'.'], 'eval_fail'),
    test('T_VARS_EFAIL_08', [var,a,;,var,b,;,a,<-,b,;,b,<-,37,;,return,a,'.'], 'eval_fail'),
    test('T_VARS_11', [var,x,;,x,<-,1,;,return,x,'.'], 1),
    test('T_VARS_12', [var,x,;,var,y,;,x,<-,1,;,y,<-,2,;,return,'(',x,+,y,')','.'] , 3),
    test('T_VARS_13', [var,x,;,var,y,;,x,<-,'(',1,+,1,+,1,')',;,return,x,'.'], 3),
    test('T_VARS_14', [var,x,;,var,y,;,var,z,;,x,<-,1,;,y,<-,2,;,z,<-,'(',x,+,y,')',;,return,z,'.'], 3),
    test('T_VARS_15', [var,x,;,var,y,;,x,<-,1,;,y,<-,2,;,return,y,'.'], 2),
    test('T_VARS_16', [var,x,;,var,y,;,x,<-,1,;,x,<-,2,;,return,x,'.'], 2),
    test('T_VARS_17', [var,x,;,var,y,;,x,<-,1,;,y,<-,1000,;,x,<-,y,;,return,x,'.'] , 1000),
    test('T_VARS_18', [var,x,;,var,y,;,x,<-,1,;,y,<-,1000,;,x,<-,y,;,y,<-,2,;,return,x,'.'], 1000),
    test('T_VARS_19', [var,x,;,x,<-,'(','(',2,+,6,+,1,')',+,1,')',;,return,x,'.'] , 10),
    test('T_VARS_20', [var,x,;,x,<-,'(','(',2,+,6,+,1,')',*,2,*,2,')',;,return,x,'.'], 36),
    test('T_VARS_21', [var,a,;,var,b,;,a,<-,5,;,b,<-,'(',a,+,5,')',;,b,<-,'(',a,+,b,')',;,return,b,'.'], 15),
    test('T_VARS_22', [var,a,;,var,b,;,b,<-,37,;,a,<-,30,;,return,b,'.'], 37),
    test('T_VARS_23', [var,b,;,b,<-,37.1245,;,return,b,'.'], 37.1245),
    writeln('').

test_VAR_ARITH :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for VAR ARITHMETIC'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_VAR_ARITH_1', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', 10, '+', 'a', '+', 'b', ')', ';', 'return', 'c', '.'], 25),
    test('T_VAR_ARITH_2', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', 10, '*', 'a', '*', 'b', ')', ';', 'return', 'c', '.'], 500),
    test('T_VAR_ARITH_3', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', 10, '-', 'a', '-', 'b', ')', ';', 'return', 'c', '.'], -5),
    test('T_VAR_ARITH_4', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', 10, '-', 'a', '+', 'b', ')', ';', 'return', 'c', '.'], 15),
    test('T_VAR_ARITH_5', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', 100, '/', 'a', '/', 'b', ')', ';', 'return', 'c', '.'], 2),
    test('T_VAR_ARITH_6', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', 100, '/', 'a', '*', 'b', ')', ';', 'return', 'c', '.'], 200),
    test('T_VAR_ARITH_7', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', 100, '+', 'a', '*', 'b', '-', 200, ')', ';', 'return', 'c', '.'], -50),
    test('T_VAR_ARITH_8', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', '(', 100, '+', 'a', ')', '*', 'b', '-', 200, ')', ';', 'return', 'c', '.'], 850),
    test('T_VAR_ARITH_9', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', '(', 10, '+', 'a', ')', '*', '(', 'b', '-', 20, ')', ')', ';', 'return', 'c', '.'], -150),
    test('T_VAR_ARITH_10', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', '(', 10, '+', 'a', ')', '+', '(', 'b', '-', 20, ')', ')', ';', 'return', 'c', '.'], 5),
    test('T_VAR_ARITH_11', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', '(', 10, '+', 'a', ')', '-', '(', 'b', '-', 20, ')', ')', ';', 'return', 'c', '.'], 25),
    test('T_VAR_ARITH_12', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', '(', 10, '+', 'a', ')', '/', '(', 'b', '-', 20, ')', ')', ';', 'return', 'c', '.'], -1.5),
    test('T_VAR_ARITH_13', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', '(', 10, '*', 'a', ')', '/', '(', 'b', '-', 15, '+', 10, ')', ')', ';', 'return', 'c', '.'], 10),
    test('T_VAR_ARITH_14', ['var', 'a', ';', 'var', 'b', ';', 'var', 'c', ';', 'a', '<-', 5, ';', 'b', '<-', '(', 'a', '+', 5, ')', ';', 'c', '<-', '(', '(', 10, '*', '(', 'a', '+', 1, ')', ')', '/', '(', '(', 'b', '-', 20, ')', '/', 2, ')', ')', ';', 'return', 'c', '.'], -12),
    writeln('').

test_LOGIC :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for LOGIC'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_LOGIC_1', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '<', 10, ')', 'then', 'out', '<-', 1, '.', 'endif', ';', 'return', 'out', '.'], 1),
    test('T_LOGIC_2', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '>', 3, ')', 'then', 'out', '<-', 1, '.', 'endif', ';', 'return', 'out', '.'], 1),
    test('T_LOGIC_3', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '==', 5, ')', 'then', 'out', '<-', 1, '.', 'endif', ';', 'return', 'out', '.'], 1),
    test('T_LOGIC_4', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '!=', 10, ')', 'then', 'out', '<-', 1, '.', 'endif', ';', 'return', 'out', '.'], 1),
    test('T_LOGIC_5', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '<=', 10, ')', 'then', 'out', '<-', 1, '.', 'endif', ';', 'return', 'out', '.'], 1),
    test('T_LOGIC_6', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '<=', 5, ')', 'then', 'out', '<-', 1, '.', 'endif', ';', 'return', 'out', '.'], 1),
    test('T_LOGIC_7', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '>=', 2, ')', 'then', 'out', '<-', 1, '.', 'endif', ';', 'return', 'out', '.'], 1),
    test('T_LOGIC_8', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '>=', 5, ')', 'then', 'out', '<-', 1, '.', 'endif', ';', 'return', 'out', '.'], 1),
    test('T_LOGIC_9', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '<', 3, ')', 'then', 'out', '<-', 1, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'return', 'out', '.'], 0),
    test('T_LOGIC_10', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '>', 10, ')', 'then', 'out', '<-', 1, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'return', 'out', '.'], 0),
    test('T_LOGIC_11', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '<=', 3, ')', 'then', 'out', '<-', 1, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'return', 'out', '.'], 0),
    test('T_LOGIC_12', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '>=', 10, ')', 'then', 'out', '<-', 1, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'return', 'out', '.'], 0),
    test('T_LOGIC_13', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '==', 3, ')', 'then', 'out', '<-', 1, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'return', 'out', '.'], 0),
    test('T_LOGIC_14', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '!=', 5, ')', 'then', 'out', '<-', 1, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'return', 'out', '.'], 0),
    test('T_LOGIC_15', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '<', 3, ')', 'then', 'out', '<-', 1, '.', 'else', 'if', '(', 'x', '>', 3, ')', 'then', 'out', '<-', 2, '.', 'else', 'out', '<-', 0, '.', 'endif', '.', 'endif', ';', 'return', 'out', '.'], 2),
    test('T_LOGIC_16', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '<', 3, ')', 'then', 'out', '<-', 1, '.', 'else', 'if', '(', 'x', '>', 3, ')', 'then', 'out', '<-', 2, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'out', '<-', '(', 'out', '+', 2, ')', '.', 'endif', ';', 'return', 'out', '.'], 4),
    test('T_LOGIC_17', ['var', 'x', '<-', 5, ';', 'var', 'y', '<-', 3, ';', 'var', 'out', ';', 'if', '(', '(', 'x', '>=', 3, '&&', 'y', '<=', 3, ')', ')', 'then', 'out', '<-', 1, '.', 'else', 'if', '(', 'x', '>', 3, ')', 'then', 'out', '<-', 2, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'out', '<-', '(', 'out', '+', 2, ')', '.', 'endif', ';', 'return', 'out', '.'], 1),
    test('T_LOGIC_18', ['var', 'x', '<-', 5, ';', 'var', 'y', '<-', 3, ';', 'var', 'w', '<-', 1, ';', 'var', 'z', '<-', 2, ';', 'var', 'out', ';', 'if', '(', '(', '(', 'x', '>=', 3, '&&', 'y', '<=', 3, ')', '&&', 'z', '==', 2, ')', ')', 'then', 'out', '<-', 1, '.', 'else', 'if', '(', 'x', '>', 3, ')', 'then', 'out', '<-', 2, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'out', '<-', '(', 'out', '+', 2, ')', '.', 'endif', ';', 'return', 'out', '.'], 1),
    test('T_LOGIC_19', ['var', 'x', '<-', 5, ';', 'var', 'y', '<-', 3, ';', 'var', 'w', '<-', 1, ';', 'var', 'z', '<-', 2, ';', 'var', 'out', ';', 'if', '(', '(', '(', 'x', '>=', 3, '&&', 'y', '<=', 3, ')', '&&', '(', 'z', '==', 2, '&&', 'w', '==', 1, ')', ')', ')', 'then', 'out', '<-', 1, '.', 'else', 'if', '(', 'x', '>', 3, ')', 'then', 'out', '<-', 2, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'out', '<-', '(', 'out', '+', 2, ')', '.', 'endif', ';', 'return', 'out', '.'], 1),
    writeln('').

test_IF_THEN :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for IF THEN'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_IF_THEN_1', ['var', 'x', ';', 'x', '<-', -1, ';', 'if', '(', 'x', '!=', 0, ')', 'then', 'x', '<-', 10, '.', 'endif', ';', 'return', 'x', '.'], 10),
    test('T_IF_THEN_2', ['var', 'x', ';', 'x', '<-', 1, ';', 'if', '(', 'x', '==', 0, ')', 'then', 'x', '<-', 10, '.', 'endif', ';', 'return', 'x', '.'], 1),
    test('T_IF_THEN_3', ['var', 'x', ';', 'x', '<-', 1, ';', 'if', '(', '(', 'x', '<', 0, '&&', 'x', '>', 1, ')', ')', 'then', 'x', '<-', 10, '.', 'endif', ';', 'return', 'x', '.'], 1),
    %% test('T_IF_THEN_4', ['var', 'x', ';', 'x', '<-', 1, ';', 'if', '(', '(', '(', 'x', '<=', 0, '&&', 'x', '>=', 1,')', '||', '(', 'x', '==', 1, ')', ')', ')', 'then', 'x', '<-', 10, '.', 'endif', ';', 'return', 'x', '.'], 10),
    writeln('').

test_IF_THEN_ELSE :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for IF THEN ELSE'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_IF_THEN_ELSE_1', ['var', 'x', ';', 'x', '<-', 1, ';', 'if', '(', 'x', '<', 0, ')', 'then', 'x', '<-', 10, '.', 'else', 'x', '<-', 20, '.', 'endif', ';', 'return', 'x', '.'], 20),
    test('T_IF_THEN_ELSE_2', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '<', 3, ')', 'then', 'out', '<-', 1, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'return', 'out', '.'], 0),
    test('T_IF_THEN_ELSE_3', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '>=', 3, ')', 'then', 'out', '<-', 1, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'return', 'out', '.'], 1),
    test('T_IF_THEN_ELSE_4', ['var', 'x', '<-', 3, ';', 'var', 'out', ';', 'if', '(', 'x', '<', 3, ')', 'then', 'out', '<-', 1, '.', 'else', 'if', '(', 'x', '>', 3, ')', 'then', 'out', '<-', 2, '.', 'else', 'out', '<-', 0, '.', 'endif', '.', 'endif', ';', 'return', 'out', '.'], 0),
    test('T_IF_THEN_ELSE_5', ['var', 'x', '<-', 5, ';', 'var', 'out', ';', 'if', '(', 'x', '<', 3, ')', 'then', 'out', '<-', 1, '.', 'else', 'if', '(', 'x', '>', 3, ')', 'then', 'out', '<-', 2, '.', 'else', 'out', '<-', 0, '.', 'endif', ';', 'out', '<-', '(', 'out', '+', 2, ')', '.', 'endif', ';', 'return', 'out', '.'], 4),
    writeln('').

test_WHILE_DO_DONE :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for WHILE DO DONE'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
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
    writeln('').

test_FUNCTION :- 
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for FUNCTION DECLARATION AND FUNCTION CALLS'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_FUNC_1', ['function', 'f', '(', 'x', ')', '{', 'return', 'x', '.', '}', ';', 'return', 'f', '(', 10 , ')', '.'], 10),
    test('T_FUNC_2', ['function', 'f', '(', 'x', ')', '{', 'return', 'x', '.', '}', ';', 'return', 'f', '(', '(', 10, '+', 1, ')', ')', '.'], 11),
    test('T_FUNC_3', ['function', 'f', '(', 'x', ')', '{', 'return', '(','x', '+', 1, ')', '.', '}', ';', 'return', 'f', '(', 10 , ')', '.'], 11),
    test('T_FUNC_4', ['function', 'foo', '(', 'x', ')', '{', 'var', 'out', '<-', '(', 'x', '*', 2, ')', ';', 'return', 'out', '.', '}', ';', 'return', 'foo', '(', 2, ')', '.'], 4),
    test('T_FUNC_5', ['var', 'x', '<-', 1, ';', 'function', 'foo', '(', 'x', ')', '{', 'var', 'out', '<-', '(', 'x', '*', 2, ')', ';', 'return', 'out', '.', '}', ';', 'var', 'z', '<-', 'foo', '(', 'x', ')', ';', 'return', 'z', '.'], 2),
    test('T_FUNC_6', ['var', 'x', '<-', 0, ';', 'function', 'x', '(', 'x', ')', '{', 'return', 'x', '.', '}', ';', 'return', 'x', '(', 'x', ')', '.'], 0),
    writeln('').

test_NESTED_FUNCTION :- 
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for NESTED_FUNCTION'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    %test('T_NESTED_FUNC_1', ['var', 'x', '<-', 0, ';', 'function', 'foo', '(', 'x', ')', '{', 'function', 'foo1', '(', 'y', ')', '{', 'return', 'x', '.', '}', ';', 'return', 'foo1', '(', 2, ')', '.', '}', ';', 'return', 'foo', '(', 1, ')', '.'], 1),
    %test('T_NESTED_FUNC_2', ['var', 'x', '<-', 0, ';', 'function', 'foo', '(', 'z', ')', '{', 'function', 'foo1', '(', 'y', ')', '{', 'return', 'x', '.', '}', ';', 'return', 'foo1', '(', 2, ')', '.', '}', ';', 'return', 'foo', '(', 1, ')', '.'], 0),
    writeln('').


test_STRESS :-
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    writeln('% Test Cases for STRESS TESTING'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_FIBONACCI_S_10', ['function', 'fib', '(', 'n', ')', '{', 'var', 'out', '<-', 0, ';', 'if', '(', 'n', '==', 0, ')', 'then', 'out', '<-', 0, '.', 'else', 'if', '(', 'n', '==', 1, ')', 'then', 'out', '<-', 1, '.', 'else', 'out', '<-', '(', 'fib', '(', '(', 'n', '-', 1, ')', ')', '+', 'fib', '(', '(', 'n', '-', 2, ')', ')', ')', '.', 'endif', '.', 'endif', ';', 'return', 'out', '.', '}', ';', 'return', 'fib', '(', 10, ')', '.'], 55),
    test('T_FIBONACCI_M_16', ['function', 'fib', '(', 'n', ')', '{', 'var', 'out', '<-', 0, ';', 'if', '(', 'n', '==', 0, ')', 'then', 'out', '<-', 0, '.', 'else', 'if', '(', 'n', '==', 1, ')', 'then', 'out', '<-', 1, '.', 'else', 'out', '<-', '(', 'fib', '(', '(', 'n', '-', 1, ')', ')', '+', 'fib', '(', '(', 'n', '-', 2, ')', ')', ')', '.', 'endif', '.', 'endif', ';', 'return', 'out', '.', '}', ';', 'return', 'fib', '(', 16, ')', '.'], 987),
    test('T_FIBONACCI_XL_300', ['function', 'fib', '(', 'n', ')', '{', 'var', 'count', '<-', 1, ';', 'var', 'fib', '<-', 1, ';', 'var', 'num1', '<-', 0,';','var','num2','<-',1, ';', 'while', '(', 'count', '!=', 'n', ')', 'do', 'count', '<-', '(', 'count', '+', 1, ')', ';', 'fib', '<-', '(', 'num1', '+', 'num2', ')', ';', 'num1', '<-', 'num2', ';', 'num2', '<-', 'fib', '.', 'done', ';','return' , 'fib','.','}', ';', 'return', 'fib', '(', 300, ')', '.'], 222232244629420445529739893461909967206666939096499764990979600),
    test('T_FIBONACCI_XXL_500', ['function', 'fib', '(', 'n', ')', '{', 'var', 'count', '<-', 1, ';', 'var', 'fib', '<-', 1, ';', 'var', 'num1', '<-', 0,';','var','num2','<-',1, ';', 'while', '(', 'count', '!=', 'n', ')', 'do', 'count', '<-', '(', 'count', '+', 1, ')', ';', 'fib', '<-', '(', 'num1', '+', 'num2', ')', ';', 'num1', '<-', 'num2', ';', 'num2', '<-', 'fib', '.', 'done', ';','return' , 'fib','.','}', ';', 'return', 'fib', '(', 500, ')', '.'], 139423224561697880139724382870407283950070256587697307264108962948325571622863290691557658876222521294125),
    test('T_FIBONACCI_TEXAS_LARGE_20000', ['function', 'fib', '(', 'n', ')', '{', 'var', 'count', '<-', 1, ';', 'var', 'fib', '<-', 1, ';', 'var', 'num1', '<-', 0,';','var','num2','<-',1, ';', 'while', '(', 'count', '!=', 'n', ')', 'do', 'count', '<-', '(', 'count', '+', 1, ')', ';', 'fib', '<-', '(', 'num1', '+', 'num2', ')', ';', 'num1', '<-', 'num2', ';', 'num2', '<-', 'fib', '.', 'done', ';','return' , 'fib','.','}', ';', 'return', 'fib', '(', 20000, ')', '.'],  2531162323732361242240155003520607291766356485802485278951929841991312781760541315230153423463758831637443488219211037689033673531462742885329724071555187618026931630449193158922771331642302030331971098689235780843478258502779200293635651897483309686042860996364443514558772156043691404155819572984971754278513112487985892718229593329483578531419148805380281624260900362993556916638613939977074685016188258584312329139526393558096840812970422952418558991855772306882442574855589237165219912238201311184749075137322987656049866305366913734924425822681338966507463855180236283582409861199212323835947891143765414913345008456022009455704210891637791911265475167769704477334859109822590053774932978465651023851447920601310106288957894301592502061560528131203072778677491443420921822590709910448617329156135355464620891788459566081572824889514296350670950824208245170667601726417091127999999941149913010424532046881958285409468463211897582215075436515584016297874572183907949257286261608612401379639484713101138120404671732190451327881433201025184027541696124114463488665359385870910331476156665889459832092710304159637019707297988417848767011085425271875588008671422491434005115288334343837778792282383576736341414410248994081564830202363820504190074504566612515965134665683289356188727549463732830075811851574961558669278847363279870595320099844676879457196432535973357128305390290471349480258751812890314779723508104229525161740643984423978659638233074463100366500571977234508464710078102581304823235436518145074482824812996511614161933313389889630935320139507075992100561077534028207257574257706278201308302642634678112591091843082665721697117838726431766741158743554298864560993255547608496686850185804659790217122426535133253371422250684486113457341827911625517128815447325958547912113242367201990672230681308819195941016156001961954700241576553750737681552256845421159386858399433450045903975167084252876848848085910156941603293424067793097271128806817514906531652407763118308162377033463203514657531210413149191213595455280387631030665594589183601575340027172997222489081631144728873621805528648768511368948639522975539046995395707688938978847084621586473529546678958226255042389998718141303055036060772003887773038422366913820397748550793178167220193346017430024134496141145991896227741842515718997898627269918236920453493946658273870473264523119133765447653295022886429174942653014656521909469613184983671431465934965489425515981067546087342348350724207583544436107294087637975025147846254526938442435644928231027868701394819091132912397475713787593612758364812687556725146456646878912169274219209708166678668152184941578590201953144030519381922273252666652671717526318606676754556170379350956342095455612780202199922615392785572481747913435560866995432578680971243966868110016581395696310922519803685837460795358384618017215468122880442252343684547233668502313239328352671318130604247460452134121833305284398726438573787798499612760939462427922917659263046333084007208056631996856315539698234022953452211505675629153637867252695056925345220084020071611220575700841268302638995272842160994219632684575364180160991884885091858259996299627148614456696661412745040519981575543804847463997422326563897043803732970397488471644906183310144691243649149542394691524972023935190633672827306116525712882959108434211652465621144702015336657459532134026915214509960877430595844287585350290234547564574848753110281101545931547225811763441710217452979668178025286460158324658852904105792472468108996135476637212057508192176910900422826969523438985332067597093454021924077101784215936539638808624420121459718286059401823614213214326004270471752802725625810953787713898846144256909835116371235019527013180204030167601567064268573820697948868982630904164685161783088076506964317303709708574052747204405282785965604677674192569851918643651835755242670293612851920696732320545562286110332140065912751551110134916256237884844001366366654055079721985816714803952429301558096968202261698837096090377863017797020488044826628817462866854321356787305635653577619877987998113667928954840972022833505708587561902023411398915823487627297968947621416912816367516125096563705174220460639857683971213093125),
    test('T_FACTORIAL_S_4', ['var', 'y', '<-', 1, ';', 'function', 'fact', '(', 'x', ')', '{', 'var', 'result', '<-', 1, ';', 'if', '(', 'x', '==', 1, ')', 'then', 'result', '<-', 1, '.', 'else', 'result', '<-', '(', 'x', '*', 'fact', '(', '(', 'x', '-', 1, ')', ')', ')', '.', 'endif', ';', 'return', 'result', '.', '}', ';', 'return', 'fact', '(', 4, ')', '.'], 24),
    test('T_FACTORIAL_M_66', ['var', 'y', '<-', 1, ';', 'function', 'fact', '(', 'x', ')', '{', 'var', 'result', '<-', 1, ';', 'if', '(', 'x', '==', 1, ')', 'then', 'result', '<-', 1, '.', 'else', 'result', '<-', '(', 'x', '*', 'fact', '(', '(', 'x', '-', 1, ')', ')', ')', '.', 'endif', ';', 'return', 'result', '.', '}', ';', 'return', 'fact', '(', 66, ')', '.'], 544344939077443064003729240247842752644293064388798874532860126869671081148416000000000000000),
    test('T_FACTORIAL_L_150', ['var', 'y', '<-', 1, ';', 'function', 'fact', '(', 'x', ')', '{', 'var', 'result', '<-', 1, ';', 'if', '(', 'x', '==', 1, ')', 'then', 'result', '<-', 1, '.', 'else', 'result', '<-', '(', 'x', '*', 'fact', '(', '(', 'x', '-', 1, ')', ')', ')', '.', 'endif', ';', 'return', 'result', '.', '}', ';', 'return', 'fact', '(', 150, ')', '.'], 57133839564458545904789328652610540031895535786011264182548375833179829124845398393126574488675311145377107878746854204162666250198684504466355949195922066574942592095735778929325357290444962472405416790722118445437122269675520000000000000000000000000000000000000),
    test('T_FACTORIAL_XXL_1000', ['var', 'y', '<-', 1, ';', 'function', 'fact', '(', 'x', ')', '{', 'var', 'result', '<-', 1, ';', 'if', '(', 'x', '==', 1, ')', 'then', 'result', '<-', 1, '.', 'else', 'result', '<-', '(', 'x', '*', 'fact', '(', '(', 'x', '-', 1, ')', ')', ')', '.', 'endif', ';', 'return', 'result', '.', '}', ';', 'return', 'fact', '(', 1000, ')', '.'], 402387260077093773543702433923003985719374864210714632543799910429938512398629020592044208486969404800479988610197196058631666872994808558901323829669944590997424504087073759918823627727188732519779505950995276120874975462497043601418278094646496291056393887437886487337119181045825783647849977012476632889835955735432513185323958463075557409114262417474349347553428646576611667797396668820291207379143853719588249808126867838374559731746136085379534524221586593201928090878297308431392844403281231558611036976801357304216168747609675871348312025478589320767169132448426236131412508780208000261683151027341827977704784635868170164365024153691398281264810213092761244896359928705114964975419909342221566832572080821333186116811553615836546984046708975602900950537616475847728421889679646244945160765353408198901385442487984959953319101723355556602139450399736280750137837615307127761926849034352625200015888535147331611702103968175921510907788019393178114194545257223865541461062892187960223838971476088506276862967146674697562911234082439208160153780889893964518263243671616762179168909779911903754031274622289988005195444414282012187361745992642956581746628302955570299024324153181617210465832036786906117260158783520751516284225540265170483304226143974286933061690897968482590125458327168226458066526769958652682272807075781391858178889652208164348344825993266043367660176999612831860788386150279465955131156552036093988180612138558600301435694527224206344631797460594682573103790084024432438465657245014402821885252470935190620929023136493273497565513958720559654228749774011413346962715422845862377387538230483865688976461927383814900140767310446640259899490222221765904339901886018566526485061799702356193897017860040811889729918311021171229845901641921068884387121855646124960798722908519296819372388642614839657382291123125024186649353143970137428531926649875337218940694281434118520158014123344828015051399694290153483077644569099073152433278288269864602789864321139083506217095002597389863554277196742822248757586765752344220207573630569498825087968928162753848863396909959826280956121450994871701244516461260379029309120889086942028510640182154399457156805941872748998094254742173582401063677404595741785160829230135358081840096996372524230560855903700624271243416909004153690105933983835777939410970027753472000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    writeln('').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% MAIN: ENTRY POINT 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

main :- 
    test_PARSE_FAIL,
    test_EVAL_FAIL,
    test_PAREN,
    test_ARITHMETIC,
    test_DECASSIGN,
    test_VARIABLE,
    test_LOGIC,
    test_IF_THEN,
    test_IF_THEN_ELSE,
    test_WHILE_DO_DONE,
    test_FUNCTION,
    test_NESTED_FUNCTION,
    test_STRESS,
    true.

