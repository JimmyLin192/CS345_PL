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
    \+ get_assoc(FUNC_NAME, VARS, _),
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
    ansi_format([faint, fg(cyan)], '[~w]: Pass - Parse Fail As Expected. \n', [Name]).

test(Name, Tokens, Expected) :- 
    parse(Tokens, AST), 
    \+ evaluate(AST, _),  
    ( Expected == 'eval_fail' | Expected == 'evaluate_fail'), 
        ansi_format([faint, fg(cyan)], '[~w]: Pass - Evaluate Fail As Expected. \n', [Name]).

test(Name, Tokens, Expected) :- 
    parse(Tokens, AST), evaluate(AST, X), (
        ( X \== Expected, 
            ansi_format([bold, fg(red)], '[~w]: Fail.', [Name]),
            write(' Result: '), write(X), 
            write(', Expected: '), writeln(Expected) )  
     |  ( X == Expected, 
        ansi_format([faint, fg(cyan)], '[~w]: Pass. \n', [Name])
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
    writeln('% Test Cases for function declaration and function calls'),
    writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
    test('T_FUNC_1', ['function', 'f', '(', 'x', ')', '{', 'return', 'x', '.', '}', ';', 'return', 'f', '(', 10 , ')', '.'], 10),
    test('T_FUNC_2', ['function', 'f', '(', 'x', ')', '{', 'return', 'x', '.', '}', ';', 'return', 'f', '(', '(', 10, '+', 1, ')', ')', '.'], 11),
    test('T_FUNC_3', ['function', 'f', '(', 'x', ')', '{', 'return', '(','x', '+', 1, ')', '.', '}', ';', 'return', 'f', '(', 10 , ')', '.'], 11),
    test('T_FUNC_4', ['function', 'foo', '(', 'x', ')', '{', 'var', 'out', '<-', '(', 'x', '*', 2, ')', ';', 'return', 'out', '.', '}', ';', 'return', 'foo', '(', 2, ')', '.'], 4),
    test('T_FUNC_5', ['var', 'x', '<-', 1, ';', 'function', 'foo', '(', 'x', ')', '{', 'var', 'out', '<-', '(', 'x', '*', 2, ')', ';', 'return', 'out', '.', '}', ';', 'var', 'z', '<-', 'foo', '(', 'x', ')', ';', 'return', 'z', '.'], 2),
    %%test('T_FUNC_6', ['var', 'x', '<-', 0, ';', 'function', 'x', '(', 'x', ')', '{', 'return', 'x', '.', '}', ';', 'return', 'x', '(', 'x', ')', '.'], 0),
    writeln('').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% MAIN: ENTRY POINT 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

main :- 
    test_PARSE_FAIL,
    test_EVAL_FAIL,
    test_PAREN,
    test_ARITHMETIC,
    test_LOGIC,
    test_IF_THEN,
    test_IF_THEN_ELSE,
    test_WHILE_DO_DONE,
    test_FUNCTION,
    true.




















