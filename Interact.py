import pexpect

EXEC = "./des"
PROMPT = "DES>"
PATH = "./examples/"
proc = pexpect.spawn(EXEC)
proc.expect(PROMPT)
proc.sendline("/consult "+PATH+"bom.dl")
proc.expect(PROMPT)
proc.sendline("assembly(X,Y,Z)")
proc.expect(PROMPT)
x = proc.before
with open("out.txt",'w') as f:
	f.write(x+"\n")
