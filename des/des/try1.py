import pexpect
child = pexpect.spawn('./des')
child.expect('DES>')
child.sendline('/consult ./examples/bom.dl')
child.expect('DES>')
child.sendline('/save_ddb db.dl')
child.expect('DES>')