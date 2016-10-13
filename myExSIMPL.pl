parse(TokenList, AST) :- phrase(program(AST), TokenList, []).

/* Keyword Declarations */
keyword(['.', ';']).   % statement terminator
keyword(['(', ')']).   % parentheses
keyword(['{', '}']).   % brackets
keyword(['<-']).       % assignment
keyword(['+', '-']).   % addOp
keyword(['*', '/']).   % mulOp
keyword(['var', 'return']).           % reserved words
keyword(['if', 'else', 'then']).     % conditions
keyword(['while', 'do', 'done']).    % loop
keyword(['&&', '||']).     % logOp
keyword(['==', '<', '>', '<=', '>=', '!=']).  % comparator

/* Program recursive definition */
program(prog(declaration(NAME), PROGRAM)) --> [var], identity(NAME), [';'], program(PROGRAM).
program(prog(assignment(NAME, VALUE), PROGRAM)) --> identity(NAME), ['<-'], base(VALUE), [';'], program(PROGRAM).
program(prog(decAssignment(NAME, VALUE), PROGRAM)) --> [var], identity(NAME), ['<-'], base(VALUE), [';'], program(PROGRAM).
program(prog(retStatement(VALUE))) --> [return], base(VALUE), ['.'].  % terminal statement
/* Element-wise rule definition */
base(NAME) --> identity(NAME) | numerics(NAME) | ['('], expression(NAME), [')'].
expression(EXP) --> term(EXP) | term(TERM), ['+'], left_assoc(EXP, TERM, addition) | term(TERM), ['-'], left_assoc(EXP, TERM, subtraction).
term(TERM) --> factor(TERM) | factor(VALUE), ['*'], left_assoc(TERM, VALUE, multiplication) | factor(VALUE), ['/'], left_assoc(TERM, VALUE, division).
factor(FACTOR) --> base(FACTOR).
identity(NAME) --> [NAME], { keyword(Keyword), \+ member(NAME, Keyword), \+ number(NAME) }.
numerics(VALUE) --> [VALUE], { number(VALUE) }.
/* left_assoc for math compuation */
% for every computational operators, 
% the first rule is the terminal rule (not generating more non-terminal)
% while the second rule is the recursive rule
left_assoc(compute(addition,TERM_A,TERM_B), TERM_A, addition) --> term(TERM_B).
left_assoc(EXP, TERM_A, addition) --> term(TERM_B), ['+'], left_assoc(EXP, compute(addition, TERM_A, TERM_B), addition).
left_assoc(compute(subtraction,TERM_A,TERM_B), TERM_A, subtraction) --> term(TERM_B).
left_assoc(EXP, TERM_A, subtraction) --> term(TERM_B), ['-'], left_assoc(EXP, compute(subtraction, TERM_A, TERM_B), subtraction).
left_assoc(compute(multiplication,TERM_A,TERM_B), TERM_A, multiplication) --> factor(TERM_B).
left_assoc(EXP, TERM_A, multiplication) --> term(TERM_B), ['*'], left_assoc(EXP, compute(multiplication, TERM_A, TERM_B), multiplication).
left_assoc(compute(division,TERM_A,TERM_B), TERM_A, division) --> factor(TERM_B).
left_assoc(EXP, TERM_A, division) --> term(TERM_B), ['/'], left_assoc(EXP, compute(division,TERM_A, TERM_B), division).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
evaluate(AST, Number) :- empty_assoc(VARIABLES), empty_assoc(FUNCTIONS), validate(AST, Number, VARIABLES, _, FUNCTIONS, _).

% validate an empty program or statement
validate([], _, VAR, VAR, FUNC, FUNC).
% validate a literal number as it is
validate(X, X, VAR, VAR, FUNC, FUNC) :- number(X).
% validate a declared variable
validate(X, OUTCOME, VAR, VAR, FUNC, FUNC) :- get_assoc(X, VAR, OUTCOME), OUTCOME \== empty.
% validate all arithmetic computations.
validate(compute(addition, OPR_A, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), OUTCOME is VAL_OPR_A + VAL_OPR_B.
validate(compute(subtraction, OPR_A, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), OUTCOME is VAL_OPR_A - VAL_OPR_B.
validate(compute(multiplication, OPR_A, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), OUTCOME is VAL_OPR_A * VAL_OPR_B.
validate(compute(division, OPR_A, OPR_B), OUTCOME, VAR, VAR, FUNC, FUNC):- validate(OPR_A, VAL_OPR_A, VAR, VAR, FUNC, FUNC), validate(OPR_B, VAL_OPR_B, VAR, VAR, FUNC, FUNC), OUTCOME is VAL_OPR_A / VAL_OPR_B.


% validate the return statement
validate(retStatement(NAME), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- validate(NAME, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
% validate the declaration statement
validate(declaration(NAME), _, PRE_VAR, POST_VAR, PRE_FUNC, PRE_FUNC) :- \+ get_assoc(NAME, PRE_VAR, _), put_assoc(NAME, PRE_VAR, empty, POST_VAR).
% validate the assignment statement
validate(assignment(NAME, VALUE), _, PRE_VAR, POST_VAR, PRE_FUNC, PRE_FUNC) :- get_assoc(NAME, PRE_VAR, _), validate(VALUE, OUTCOME, PRE_VAR, _, PRE_FUNC, _), put_assoc(NAME, PRE_VAR, OUTCOME, POST_VAR).
% validate the decAssignment 
validate(decAssignment(NAME, VALUE), _, PRE_VAR, POST_VAR, PRE_FUNC, PRE_FUNC) :- \+ get_assoc(NAME, PRE_VAR, _), validate(VALUE, OUTCOME, PRE_VAR, _, PRE_FUNC, _), put_assoc(NAME, PRE_VAR, OUTCOME, POST_VAR).

% validate the single prog node
validate(prog(PROGRAM), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- validate(PROGRAM, OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC).
% validate the prog node recursively
validate(prog(PROGRAM, AST), OUTCOME, PRE_VAR, POST_VAR, PRE_FUNC, POST_FUNC) :- validate(PROGRAM, _, PRE_VAR, VAR_C, PRE_FUNC, FUNC_C), validate(AST, OUTCOME, VAR_C, POST_VAR, FUNC_C, POST_FUNC).
