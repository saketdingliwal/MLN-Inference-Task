import stp
s = stp.Solver()
a = s.bitvec('a', 1)
b = s.bitvec('b', 1)
c = s.bitvec('c', 1)
s.add(a & c == 1)
print(s.check())
print(s.model())
