parse(TokenList, AST) :- phrase(program(AST), TokenList, []).

/* Keyword Declarations */
keyword(['.', ';']).   % statement terminator
keyword(['(', ')']).   % parentheses
keyword(['{', '}']).   % brackets
keyword(['<-']).       % assignment
keyword(['+', '-']).   % addOp
keyword(['*', '/']).   % mulOp
keyword([var, 'return']).           % reserved words
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
base(NAME) --> identifier(NAME) | numerics(NAME).
base(VALUE) --> ['('], expression(VALUE), [')'].
expression(EXP) --> term(TERM), ['+'], left_assoc(EXP, TERM, addition).
expression(EXP) --> term(TERM), ['-'], left_assoc(EXP, TERM, subtraction).
expression(EXP) --> term(EXP).
term(TERM) --> factor(VALUE), ['*'], left_assoc(TERM, VALUE, multiplication).
term(TERM) --> factor(VALUE), ['/'], left_assoc(TERM, VALUE, division).
term(TERM) --> factor(TERM).
factor(FACTOR) --> base(FACTOR).
identifier(NAME) --> [NAME], { keyword(Keyword), \+ member(NAME, Keyword), \+ number(NAME) }.
numerics(VALUE) --> [VALUE], { number(VALUE) }.
/* left_assoc for math compuation */
left_assoc(compute(addition,TERM,TERM1), TERM, addition) --> term(TERM1).
left_assoc(EXP, TERM, addition) --> term(TERM1), ['+'], left_assoc(EXP, compute(addition, TERM, TERM1), addition).
left_assoc(compute(subtraction,TERM,TERM1), TERM, subtraction) --> term(TERM1).
left_assoc(EXP, TERM, subtraction) --> term(TERM1), ['-'], left_assoc(EXP, compute(subtraction, TERM, TERM1), subtraction).
left_assoc(compute(multiplication,TERM,TERM1), TERM, multiplication) --> factor(TERM1).
left_assoc(EXP, TERM, multiplication) --> term(TERM1), ['*'], left_assoc(EXP, compute(multiplication, TERM, TERM1), multiplication).
left_assoc(compute(division,TERM,TERM1), TERM, division) --> factor(TERM1).
left_assoc(EXP, TERM, division) --> term(TERM1), ['/'], left_assoc(EXP, compute(division,TERM, TERM1), division).

