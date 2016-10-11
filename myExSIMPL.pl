parse(TokenList, AST) :- phrase(program(AST), TokenList, []).

/* Keyword Declarations */
keyword(['.', ';']).   % statement terminator
keyword(['(', ')']).   % parentheses
keyword(['{', '}']).   % brackets
keyword(['<-']).       % assignment
keyword(['+', '-']).   % addOp
keyword(['*', '/']).   % mulOp
keyword([var, return]).           % reserved words
keyword(['if', 'else', 'then']).     % conditions
keyword(['while', 'do', 'done']).    % loop
keyword(['&&', '||']).     % logOp
keyword(['==', '<', '>', '<=', '>=', '!=']).  % comparator

/* Program recursive definition */
program(prog(STATEMENT, PROGRAM)) --> statement(STATEMENT), [';'], program(PROGRAM).
/* statement-wise definition */
program(prog(retStatement(VALUE))) --> [return], base(VALUE), ['.'].  % terminal statement
statement(declaration(NAME)) --> [var], identifier(NAME).
statement(assignment(NAME, VALUE)) --> identifier(NAME), ['<-'], base(VALUE).
statement(decAssignment(NAME, VALUE)) --> [var], identifier(NAME), ['<-'], base(VALUE).
/* Element-wise rule definition */
base(NAME) --> identifier(NAME).
base(NAME) --> numerics(NAME).
base(VALUE) --> ['('], expression(VALUE), [')'].
expression(EXP) --> term(EXP).
expression(EXP) --> term(TERM), ['+'], left_assoc(EXP, TERM, addition).
expression(EXP) --> term(TERM), ['-'], left_assoc(EXP, TERM, subtraction).
term(TERM) --> factor(TERM).
term(TERM) --> factor(VALUE), ['*'], left_assoc(TERM, VALUE, multiplication).
term(TERM) --> factor(VALUE), ['/'], left_assoc(TERM, VALUE, division).
factor(FACTOR) --> base(FACTOR).
identifier(NAME) --> [NAME], { keyword(Keyword), \+ member(NAME, Keyword), \+ number(NAME) }.
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

% validate the single prog node
validate(prog(PROGRAM), OUTCOME, VAR_A, VAR_B, FUNC_A, FUNC_B) :- validate(PROGRAM, OUTCOME, VAR_A, VAR_B, FUNC_A, FUNC_B).
% validate the prog node recursively
validate(prog(STATEMENT, AST), OUTCOME, VAR_A, VAR_B, FUNC_A, FUNC_B) :- validate(STATEMENT, _, VAR_A, VAR_C, FUNC_A, FUNC_C), validate(AST, OUTCOME, VAR_C, VAR_B, FUNC_C, FUNC_B).

% validate the return statement
validate(retStatement(NAME), OUTCOME, VAR_A, VAR_B, FUNC_A, FUNC_B) :- validate(NAME, OUTCOME, VAR_A, VAR_B, FUNC_A, FUNC_B).
% validate the declaration statement
validate(declaration(NAME), _, VAR_A, VAR_B, FUNC_A, FUNC_A) :- \+ get_assoc(NAME, VAR_A, _), put_assoc(NAME, VAR_A, null, VAR_B).
% validate the assignment statement
validate(assignment(NAME, VALUE), _, VAR_A, VAR_B, FUNC_A, FUNC_A) :- get_assoc(NAME, VAR_A, _), validate(VALUE, assigned, VAR_A, _, FUNC_A, _), put_assoc(NAME, VAR_A, assigned, VAR_B).
% validate the decAssignment 
validate(decAssignment(NAME, VALUE), _, VAR_A, VAR_B, FUNC_A, FUNC_A) :- \+ get_assoc(NAME, VAR_A, _), validate(VALUE, assigned, VAR_A, _, FUNC_A, _), put_assoc(NAME, VAR_A, assigned, VAR_B).

% validate an empty program or statement
validate([], _, VAR_A, VAR_A, FUNC_A, FUNC_A).
% validate a literal number as it is
validate(X, X, VAR_A, VAR_A, FUNC_A, FUNC_A) :- number(X).
% validate a declared variable
validate(X, OUTCOME, VAR_A, VAR_A, FUNC_A, FUNC_A) :- get_assoc(X, VAR_A, OUTCOME), OUTCOME \== null.
% validate all arithmetic computations.
validate(compute(addition, OPR_A, OPR_B), OUTCOME, VAR_A, VAR_A, FUNC_A, FUNC_A):- validate(OPR_A, VAL_OPR_A, VAR_A, VAR_A, FUNC_A, FUNC_A), validate(OPR_B, VAL_OPR_B, VAR_A, VAR_A, FUNC_A, FUNC_A), OUTCOME is VAL_OPR_A + VAL_OPR_B.
validate(compute(subtraction, OPR_A, OPR_B), OUTCOME, VAR_A, VAR_A, FUNC_A, FUNC_A):- validate(OPR_A, VAL_OPR_A, VAR_A, VAR_A, FUNC_A, FUNC_A), validate(OPR_B, VAL_OPR_B, VAR_A, VAR_A, FUNC_A, FUNC_A), OUTCOME is VAL_OPR_A - VAL_OPR_B.
validate(compute(multiplication, OPR_A, OPR_B), OUTCOME, VAR_A, VAR_A, FUNC_A, FUNC_A):- validate(OPR_A, VAL_OPR_A, VAR_A, VAR_A, FUNC_A, FUNC_A), validate(OPR_B, VAL_OPR_B, VAR_A, VAR_A, FUNC_A, FUNC_A), OUTCOME is VAL_OPR_A * VAL_OPR_B.
validate(compute(division, OPR_A, OPR_B), OUTCOME, VAR_A, VAR_A, FUNC_A, FUNC_A):- validate(OPR_A, VAL_OPR_A, VAR_A, VAR_A, FUNC_A, FUNC_A), validate(OPR_B, VAL_OPR_B, VAR_A, VAR_A, FUNC_A, FUNC_A), OUTCOME is VAL_OPR_A / VAL_OPR_B.

