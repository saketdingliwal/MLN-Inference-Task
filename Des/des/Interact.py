import ply.lex as lex
import ply.yacc as yacc
import pexpect,sys
from sets import Set
cin = sys.stdin

EXEC = "./des"
PROMPT = "DES>"
PATH = ""
ARGI = 1
DOM_FILE = "dom.pl"
HARD_FILE = "Hard_Formulas.pl"
SOFT_FILE = "Soft_Formulas.pl"
# proc = pexpect.spawn(EXEC)
# proc.expect(PROMPT)
# proc.sendline("/consult "+PATH+"bom.dl")
# proc.expect(PROMPT)
# proc.sendline("assembly(X,Y,Z)")
# proc.expect(PROMPT)
# x = proc.before
# with open("out.txt",'w') as f:
# 	f.write(x+"\n")


# List of token names.   This is always required
tokens = (
	'NUMBER',
	'LPAREN',
	'RPAREN',
	'COMMA',
	'PRED',
	'VAR',
	'IMPLIES',
	'NOT'
)

# Regular expression rules for simple tokens
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_COMMA   = r','
t_PRED	  = r'[a-z][a-zA-Z]*'
t_VAR     = r'[A-Z][a-zA-Z]*'
t_IMPLIES = r'=>'
t_NOT	  = r'!'

# A regular expression rule with some action code
def t_NUMBER(t):
    r'\d+'
    t.value = int(t.value)    
    return t

# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

# A string containing ignored characters (spaces and tabs)
t_ignore  = ' \t'

# Error handling rule
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

# Build the lexer
lexer = lex.lex()

# formula := body IMPLIES head | head
# body := term | term COMMA body
# head := term
# term := NOT term | PRED LPAREN arg_seq RPAREN
# arg_seq := arg | arg COMMA arg_seq
# arg := VAR | NUMBER

start = 'formula'

def p_formula(p):
	'''formula  : body IMPLIES head 
				| head'''
	if len(p)!=2:
		p[0] = (p[1],p[3])
	else:
		p[0] = ([],p[1])

def p_body_1(p):
	'''body : term 
			| term COMMA body'''
	p[0] = [p[1]]+(p[3] if len(p)!=2 else []) 
		
def p_head(p):
	'''head : term'''
	p[0] = p[1]

def p_term(p):
	'''term : NOT term 
			| PRED LPAREN arg_seq RPAREN'''
	if len(p)==3:
		p[0] = (not p[2][0],p[2][1],p[2][2])
	else:
		p[0] = (True,p[1],p[3])

def p_argseq(p):
	'''arg_seq  : arg 
				| arg COMMA arg_seq'''
	if len(p)==2:
		p[0] = [p[1]]
	else:
		p[0] = [p[1]]+p[3]

def p_arg(p):
	'''arg : VAR 
		| NUMBER'''
	p[0] = int(p[1]) if isinstance(p[1],(int,long)) else p[1]


# Error rule for syntax errors
def p_error(p):
    print("Syntax error in input!")

data = '''
S(X),!F(1,Y)=>S(Y)
'''

parser = yacc.yacc()
# print parser.parse(data)

Preds = [("domain",1)] 				#(Symbol,Arity)
Hard_Formulas = []
Soft_Formulas = []

def tvars(term):
	# print term
	return [var for var in term[2] if not isinstance(var,(int,long))]

def fvars(formula):
	res = []
	for term in formula[0]:
		res = res + tvars(term)
	res = res + tvars(formula[1])
	return list(Set(res))

def term_to_Atom(term):
	res = []
	sign,psym,variables = term
	if not sign: res.append("not ")
	res.append(psym)
	res.append("(")
	for var in variables:
		res.append(var if not isinstance(var,(int,long)) else ("a"+str(var)))
		if var!=variables[-1]:
			res.append(",")
		else:
			res.append(")")
	return ''.join(res)

def formula_to_rule(formula,soft):
	res = []
	if soft: formula = formula[0]
	body,head = formula
	variables = fvars(formula)
	res.append(term_to_Atom(head))
	if len(body)==0 and len(variables)==0:
		return ''.join(res)
	res.append(" :- ")
	for variable in variables:
		res.append("domain("+variable+")")
		if variable!=variables[-1]:
			res.append(", ")
	for term in body:
		res.append(", ")
		res.append(term_to_Atom(term))
	return ''.join(res)	


with open(sys.argv[ARGI],'r') as f:
	n,m = map(int,f.readline().split(" "))
	for i in range(m):
		sym,arity = f.readline().split(" ")
		Preds.append((sym,int(arity)))

	hard_size,soft_size = map(int,f.readline().split(" "))
	
	for i in range(hard_size):
		text = f.readline().rstrip("\n")
		text = text.rstrip("\r")
		formula = parser.parse(text)
		Hard_Formulas.append(formula)

	for i in range(soft_size):
		text = f.readline().rstrip("\n")
		text = text.rstrip("\r")
		formula,weight = text.split("::")
		formula = parser.parse(formula)
		Soft_Formulas.append((formula,float(weight)))

with open(DOM_FILE,'w') as f:
	for i in range(n):
		f.write("domain(a"+str(i)+").\n")

with open(HARD_FILE,'w') as f:
	for formula in Hard_Formulas:
		f.write(formula_to_rule(formula,False)+".\n")

with open(SOFT_FILE,'w') as f:
	for formula in Soft_Formulas:
		f.write(formula_to_rule(formula,True)+".\n")


proc = pexpect.spawn(EXEC)
proc.expect(PROMPT)
proc.sendline("/reconsult "+PATH+DOM_FILE)
proc.expect(PROMPT)
# print proc.before		
proc.sendline("/reconsult "+PATH+HARD_FILE)
proc.expect(PROMPT)
print proc.before		

for i,formula in enumerate(Hard_Formulas):
	variables = fvars(formula)
	if len(variables)==0: continue
	sign = True
	psym = "ans"+str(i)
	head = (sign,psym,variables)
	body = ([formula[1]]+formula[0])
	des_formula = formula_to_rule((body,head),False)
	# print des_formula
	proc.sendline("/assert " + des_formula)
	proc.expect(PROMPT)
	print proc.before
	proc.sendline(term_to_Atom(head))
	proc.expect(PROMPT)
	print proc.before





