import ply.lex as lex
import ply.yacc as yacc
import pexpect,sys
from sets import Set
import re,os
cin = sys.stdin

DES_COMMAND = "./des"
PROMPT = "DES>"
PATH = ""
ARGI = 1
DOM_FILE  		= "dom.pl"
HARD_FILE 		= "Hard_Formulas.pl"
SOFT_FILE 		= "Soft_Formulas.pl"
QFILE	  		= "Model_File.pl"
WPMS_FILE 		= "WPMS_Constraints.cnf"
WPMS_MODEL_FILE = "WPMS_Model.out"
LBX_COMMAND 	= "./lbx -wm -mxapp "

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
			| PRED LPAREN args RPAREN'''
	if len(p)==3:
		p[0] = p[2].negate()
	else:
		p[0] = Term(1,p[1],p[3])

def p_args(p):
	'''args : arg_seq'''
	p[0] = tuple(p[1])

def p_argseq(p):
	'''arg_seq  : arg 
				| arg COMMA arg_seq'''
	p[0] = [p[1]]+(p[3] if len(p)!=2 else []) 

def p_arg(p):
	'''arg : VAR 
		| NUMBER'''
	p[0] = int(p[1]) if not type(p[1]) is str else p[1]


# Error rule for syntax errors
def p_error(p):
    print("Syntax error in input!")

parser = yacc.yacc()

def tvars(term):
	return [arg for arg in term.args if type(arg) is str]

def fvars(formula):
	res = []
	for term in formula.body:
		res = res + tvars(term)
	res = res + tvars(formula.head)
	return list(Set(res))

class Formula:
	def __init__(self,body,head,weight):
		self.head 		= head
		self.body 		= body
		self.weight 	= weight
		self.variables  = fvars(self)

class Term:
	def __init__(self,sign,psym,args):
		self.sign = sign
		self.psym = psym
		self.args = args
	def negate(self):
		return Term(-1*self.sign,self.psym,self.args)

def execute_Des(line):
	proc.sendline(line)
	proc.expect(PROMPT)


def term_to_Atom(term):
	res = []
	sign,psym,args = term.sign, term.psym, term.args
	if sign==-1: res.append("not ")
	res.append(psym)
	res.append("(")
	for i,arg in enumerate(args):
		res.append(arg if type(arg) is str else ("a"+str(arg)))
		if (i+1)!=len(args):
			res.append(",")
		else:
			res.append(")")
	return ''.join(res)

def formula_to_rule(formula):
	res 	  = []
	body,head = formula.body, formula.head
	variables = formula.variables
	res.append(term_to_Atom(head))
	if len(body)==0 and len(variables)==0:
		return ''.join(res)
	res.append(" :- ")
	for i,variable in enumerate(variables):
		res.append("domain("+variable+")")
		if (i+1)!=len(variables):
			res.append(", ")
	for term in body:
		res.append(", ")
		res.append(term_to_Atom(term))
	return ''.join(res)	

def parse_Output(strg):
	match 	= re.search(r'{(.*)}',strg,re.DOTALL)
	matches = re.split(",\r\n",match.groups()[0])
	matches = [match.split()[0] for match in matches if len(match.split())!=0]
	res 	= []
	for match in matches:
		x   = re.search(r'\((.*)\)',match).groups()[0].split(',')
		res.append(tuple(int(r[1:]) for r in x))
	return res

def substitute(term,vmap):
	args = tuple(vmap[arg] if type(arg) is str else arg for arg in term.args)
	return Term(term.sign,term.psym,args)

def term_to_literal(term,vmap):
	global term_to_lit,lit_to_term
	term = substitute(term,vmap)
	sign,psym,args = term.sign, term.psym, term.args
	key  = (psym,args)
	if key not in term_to_lit:
		term_to_lit[key] = len(term_to_lit)+1
		lit_to_term.append(Term(True,psym,args))
	return (sign*term_to_lit[key])

def get_clauses(Groundings,Formulas):
	clause_list,tweight = [],0
	for i,(groundings,formula) in enumerate(zip(Groundings,Formulas)):
		tweight+=(len(groundings)*formula.weight)
		variables  = formula.variables
		body,head  = formula.body, formula.head
		for grounding in groundings:
			vmap   = {x:y for x,y in zip(variables,grounding)}
			clause = [term_to_literal(head,vmap)]
			for term in body:
				clause.append(-1*term_to_literal(term,vmap))
			clause_list.append((clause,formula.weight))
	return clause_list,tweight

def WPMS_Step():
	hard_clauses,hard_weight = get_clauses(Hard_Groundings,Hard_Formulas)
	soft_clauses,soft_weight = get_clauses(Soft_Groundings,Soft_Formulas)

	clause_list = hard_clauses+soft_clauses
	nliterals   = len(term_to_lit)
	nclauses    = len(clause_list)
	with open(WPMS_FILE,'w') as f:
		f.write("p wcnf "+str(nliterals)+" "+str(nclauses)+" "+str(max_weight)+"\n")
		for clause,weight in clause_list:
			f.write(str(weight)+" ")
			for literal in clause:
				f.write(str(literal)+" ")
			f.write("0\n")
	
	os.system(LBX_COMMAND+WPMS_FILE+"> "+WPMS_MODEL_FILE)
	with open(WPMS_MODEL_FILE,'r') as f:
		output  = ''.join(f.readlines())
	model 	 	= (re.findall(r'model: (.*)\n',output)[1]).split()
	min_cost 	= int(re.findall(r'Current min MCS cost: (.*)\n',output)[0])
	Q 			= [lit_to_term[int(elem)] for elem in model if int(elem)>0]
	W 			= soft_weight - min_cost
	print [term_to_Atom(Term(term.sign,term.psym,term.args)) for term in Q]
	print W
	return Q,W



def Input():
	global n,m,max_weight,Preds,Hard_Formulas,Soft_Formulas,Hard_Groundings,Soft_Groundings
	with open(sys.argv[ARGI],'r') as f:
		n,m,max_weight = map(int,f.readline().split(" "))
		for i in range(m):
			sym,arity = f.readline().split(" ")
			Preds.append((sym,int(arity)))

		hard_size,soft_size = map(int,f.readline().split(" "))
		Hard_Groundings = [Set([]) for elem in range(hard_size)]
		Soft_Groundings = [Set([]) for elem in range(soft_size)]
		
		for i in range(hard_size):
			text 	= f.readline().rstrip("\n").rstrip("\r")
			formula = parser.parse(text)
			Hard_Formulas.append(Formula(formula[0],formula[1],max_weight))

		for i in range(soft_size):
			text 		    = f.readline().rstrip("\n").rstrip("\r")
			formula,weight  = text.split("::")
			formula 		= parser.parse(formula)
			Soft_Formulas.append(Formula(formula[0],formula[1],int(weight)))
	

def get_Groundings(i,formula,flag):
	fh 				= formula.head
	head 			= Term(1,"ans"+str(i),formula.variables)
	body 			= [Term(fh.sign*flag,fh.psym,fh.args)]+formula.body
	Query_Formula 	= Formula(body,head,max_weight)
	des_formula 	= formula_to_rule(Query_Formula)
	execute_Des("/assert "+ des_formula)
	execute_Des(term_to_Atom(head))

	groundings 		= parse_Output(proc.before)
	return groundings



def Datalog_User(flag):
	execute_Des("/consult "+PATH+DOM_FILE)
	if flag==1:
		execute_Des("/reconsult "+PATH+HARD_FILE)
	else:
		execute_Des("/reconsult "+PATH+QFILE)

	all_hard_satisfied = True

	for i,formula in enumerate(Hard_Formulas):
		if not len(formula.variables):
			if itr==0:
				all_hard_satisfied = False
			Hard_Groundings[i].update([()])
			continue
		more_groundings = get_Groundings(i,formula,flag)
		Hard_Groundings[i].update(more_groundings)
		if len(more_groundings):
			all_hard_satisfied = False
	
	if flag==1: return all_hard_satisfied

	for i,formula in enumerate(Soft_Formulas):
		if not len(formula.variables):
			Soft_Groundings.update([()])
			continue
		more_groundings = get_Groundings(i,formula,flag)
		Soft_Groundings[i].update(more_groundings)

	return all_hard_satisfied

def Init_Grounding():
	with open(DOM_FILE,'w') as f:
		for i in range(n):
			f.write("domain(a"+str(i)+").\n")

	with open(HARD_FILE,'w') as f:
		for formula in Hard_Formulas:
			f.write(formula_to_rule(formula)+".\n")

	with open(SOFT_FILE,'w') as f:
		for formula in Soft_Formulas:
			f.write(formula_to_rule(formula)+".\n")
	Datalog_User(1)

def Violations():
	with open(QFILE,'w') as f:
		for term in Q:
			formula = Formula([],term,max_weight)
			f.write(formula_to_rule(formula)+".\n")

	return Datalog_User(-1)



n,m,max_weight  = 0,0,0
Preds 			= [("domain",1)] 	#(Symbol,Arity)
Q 				= []				#Solution
W 				= 0					#Solution Weight
Hard_Formulas   = []				#H
Soft_Formulas   = []				#S
Hard_Groundings = []				#phi	
Soft_Groundings = []				#psi
lit_to_term     = [-1]
term_to_lit     = {}
proc 			= pexpect.spawn(DES_COMMAND)	#Running Datalog Solver
proc.expect(PROMPT)

itr=0
Input()
Init_Grounding()
while True:
	all_hard_satisfied = Violations()
	print Soft_Groundings
	Q_,W_ = WPMS_Step()
	if((W == W_) and all_hard_satisfied):
		break
	Q,W = Q_,W_
	itr+=1