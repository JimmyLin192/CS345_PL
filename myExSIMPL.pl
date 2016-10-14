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
condition(mulcond(COND_A, LOG_OP, COND_B)) --> ['('], condition(COND_A), logical(LOG_OP), condition(COND_B), [')'].

comparator(COMP) --> [COMP], { comparators(COMPARATORS), member(COMP, COMPARATORS) }.
logical(LOG_OP) --> [LOG_OP], { logOp(LOGIC_OPERATORS), member(LOG_OP, LOGIC_OPERATORS) }. 

/* Element-wise rule definition */
base(NAME) --> identity(NAME) | numerics(NAME) | ['('], expression(NAME), [')'].
base(funcCall(FUNC_NAME, FUNC_ARG)) --> identity(FUNC_NAME), ['('], base(FUNC_ARG), [')'].  % func call
expression(EXP) --> term(EXP) | term(TERM), ['+'], left_assoc(EXP, TERM, addition) | term(TERM), ['-'], left_assoc(EXP, TERM, subtraction).
term(TERM) --> factor(TERM) | factor(VALUE), ['*'], left_assoc(TERM, VALUE, multiplication) | factor(VALUE), ['/'], left_assoc(TERM, VALUE, division).

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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
evaluate(AST, Number) :- empty_assoc(VARIABLES), empty_assoc(FUNCTIONS), validate(AST, Number, VARIABLES, _, FUNCTIONS, _).

% validate an empty program or statement
validate([], _, VAR, VAR, FUNC, FUNC).
% validate a literal number as it is
validate(X, X, VAR, VAR, FUNC, FUNC) :- number(X).
% validate a declared variable
validate(X, OUTCOME, VAR, VAR, FUNC, FUNC) :- 
    get_assoc(X, VAR, OUTCOME), 
    OUTCOME \== empty.
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
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    OUTCOME is VAL_OPR_A / VAL_OPR_B.
% validate all logical computations
%validate(mulcond(COND_A, LOG_OP, COND_B), OUTCOME, VAR, VAR, FUNC, FUNC):- 
%    LOG_OP == ['&&'],
%    validate(COND_A, VAL_COND_A, VAR, VAR, FUNC, FUNC), 
%    validate(COND_B, VAL_COND_B, VAR, VAR, FUNC, FUNC), 
%    OUTCOME is VAL_COND_A * VAL_COND_B.
%validate(mulcond(COND_A, LOG_OP, COND_B), OUTCOME, VAR, VAR, FUNC, FUNC):- 
%    LOG_OP == ['||'], 
%    validate(COND_A, VAL_COND_A, VAR, VAR, FUNC, FUNC), 
%    validate(COND_B, VAL_COND_B, VAR, VAR, FUNC, FUNC), 
%    OUTCOME is VAL_COND_A + VAL_COND_B.
%
%% validate all comparative computations
validate(singcond(OPR_A, _, OPR_B), _, VAR, VAR, FUNC, FUNC):- 
    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
    VAL_OPR_A > VAL_OPR_B.
%validate(singcond(OPR_A, COMP_OP, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- 
%    COMP_OP is ['>='], 
%    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
%    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
%    OUTCOME is (VAL_OPR_A >= VAL_OPR_B).
%validate(singcond(OPR_A, COMP_OP, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- 
%    COMP_OP is ['<'], 
%    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
%    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
%    OUTCOME is (VAL_OPR_A < VAL_OPR_B).
%validate(singcond(OPR_A, COMP_OP, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- 
%    COMP_OP is ['<='], 
%    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
%    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
%    OUTCOME is (VAL_OPR_A =< VAL_OPR_B).
%validate(singcond(OPR_A, COMP_OP, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- 
%    COMP_OP is ['=='], 
%    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
%    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
%    OUTCOME is (VAL_OPR_A =:= VAL_OPR_B).
%validate(singcond(OPR_A, COMP_OP, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- 
%    COMP_OP == ['!='], 
%    validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), 
%    validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), 
%    OUTCOME is (VAL_OPR_A =\= VAL_OPR_B).

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
% validate the conditional
validate(conditional(COND, BRANCH_IF), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    validate(COND, _, PRE_VAR, PRE_VAR, PRE_FUNC, PRE_FUNC),
    validate(BRANCH_IF, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
%validate(conditional(COND, _), _, PRE_VAR, _, PRE_FUNC, _) :- 
%    \+ validate(COND, _, PRE_VAR, PRE_VAR, PRE_FUNC, PRE_FUNC).
%COND_OUTCOME \== true.
%validate(conditional(COND, IF_BRANCH, _), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
%    validate(COND, COND_OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC), 
%    validate(IF_BRANCH, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC), 
%    COND_OUTCOME =:= true. 
%validate(conditional(COND, _, ELSE_BRANCH), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
%    validate(COND, COND_OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC), 
%    validate(ELSE_BRANCH, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC), 
%    COND_OUTCOME =\= true.

% validate the loop
% validate sseq
validate(sseq(STATEMENT), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    validate(STATEMENT, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
validate(sseq(STATEMENT, REMAINDERS), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    validate(STATEMENT, _, PRE_VAR, IME_VAR, PRE_FUNC, IME_FUNC), 
    validate(REMAINDERS, OUTCOME, IME_VAR, POST_VAR, IME_FUNC, POST_FUNC).

% validate the single prog node
validate(prog(PROGRAM), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    validate(PROGRAM, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
% validate the prog node recursively
validate(prog(PROGRAM, AST), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- 
    validate(PROGRAM, _, PRE_VAR, VAR_C, PRE_FUNC, FUNC_C), 
    validate(AST, OUTCOME, VAR_C, POST_VAR, FUNC_C, POST_FUNC).
