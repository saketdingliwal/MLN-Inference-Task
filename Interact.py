import ply.lex as lex
import ply.yacc as yacc
import pexpect,sys
cin = sys.stdin

EXEC = "./des"
PROMPT = "DES>"
PATH = "./examples/"
ARGI = 1
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
	'WORD',
	'IMPLIES',
	'NOT'
)

# Regular expression rules for simple tokens
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_COMMA   = r','
t_WORD    = r'[A-Z][a-z]*'
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
# term := NOT term | WORD LPAREN arg_seq RPAREN
# arg_seq := arg | arg COMMA arg_seq
# arg := WORD | NUMBER

start = 'formula'

def p_formula(p):
	'''formula  : body IMPLIES head 
				| head'''
	p[0] = (p[1] if len(p)!=2 else [],p[3])

def p_body_1(p):
	'''body : term 
			| term COMMA body'''
	p[0] = [p[1]]+p[3] if len(p)!=2 else [] 
		
def p_head(p):
	'''head : term'''
	p[0] = p[1]

def p_term(p):
	'''term : NOT term 
			| WORD LPAREN arg_seq RPAREN'''
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
	'''arg : WORD 
		| NUMBER'''
	p[0] = int(p[1]) if isinstance(p[1],(int,long)) else p[1]


# Error rule for syntax errors
def p_error(p):
    print("Syntax error in input!")

data = '''
S(X),!F(1,Y)=>S(Y)
'''

parser = yacc.yacc()
print parser.parse(data)

Preds = [] 				#(Symbol,Arity)
Hard_Formulas = []
Soft_Formulas = []

with open(sys.argv[ARGI],'r') as f:
	n,m = map(int,f.readline().split(" "))
	for i in range(m):
		sym,arity = f.readline().split(" ")
		Preds.append((sym,int(arity)))

	hard_size,soft_size = map(int,f.readline().split(" "))
	
	for i in range(hard_size):
		text = f.readline()
		Hard_Formulas.append(parser.parse(text))

	for i in range(soft_size):
		text = f.readline()
		formula,weight = text.split("::")
		Soft_Formulas.append((parser.parse(formula),weight))







