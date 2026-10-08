"""Independent integer-profile checks for the exact certificate producer."""
import importlib.util
from pathlib import Path
from fractions import Fraction as Q
import unittest

SPEC = importlib.util.spec_from_file_location('profile', Path(__file__).parents[1]/'lambert_profile.py')
profile = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(profile)


def deficit(K, n):
    return sum(K-j*n for j in range(1, K//n+1))


def exponent(h, A, b, d, s, N, n):
    h,A,b,d,s = (v*N for v in (h,A,b,d,s))
    # Count interval intersections with eligible residue blocks directly.
    R = sum(max(0, min(s+h+A,(j+1)*n)-max(s,j*n+d))
            for j in range(1, (s+h+A)//n+1)) if d<n else 0
    T = max(0,b+h+d-max(b,n))
    return h+deficit(h+d,n)+deficit(A,n)-max(deficit(h+d+A,2*n),h-R-T,0)


def transport(h,A,d,N,n):
    return deficit((h+A)*N,n)+deficit(d*N,n)-deficit((h+d)*N,n)-deficit(A*N,n)


class ProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cells=profile.generate()

    def test_exact_file(self):
        target=Path(__file__).parents[2]/'Lambert/Refinement/ProfileData.lean'
        self.assertEqual(profile.render(self.cells).encode(),target.read_bytes())

    def test_intervals_and_rounding(self):
        end=Q(0)
        for l,u,j,a,b,mass in self.cells:
            self.assertLessEqual(end,l)
            self.assertLess(l,u)
            self.assertGreaterEqual(min(a+b*l,a+b*u),0)
            integral=a*(u*u-l*l)/2+b*(u**3-l**3)/3
            self.assertLessEqual(Q(mass,10**12),integral)
            self.assertLess(integral,Q(mass+1,10**12))
            end=u
        self.assertGreaterEqual(sum(c[-1] for c in self.cells),30625855746750000000)

    def test_integer_profiles(self):
        _,states=profile.expressions(500,27,516,41)
        N=10**9
        for l,u,j,a,b,_ in self.cells:
            # Interior points near both ends and the midpoint, at a distinct scale.
            for x in ((3*l+u)/4,(l+u)/2,(l+3*u)/4):
                n=int(x*N)
                self.assertLess(l*N,n)
                self.assertLess(n,u*N)
                t=transport(500,0,16,N,n)
                v=transport(500,41,25,N,n)
                w=transport(500,27,43,N,n)
                offsets=[0,t,w,v+w,w+v+t,v+t]
                raw=exponent(500,*states[j],N,n)-offsets[j]
                correction=500*N+deficit(516*N,n)-deficit(516*N,2*n)-max(raw,0)
                self.assertEqual(correction,a*N+b*n)

    def test_retuning(self):
        cells=profile.generate(50,3,52,4,Q(1))
        self.assertTrue(cells)
        self.assertNotEqual(cells,self.cells)
        with self.assertRaises(ValueError):
            profile.generate(50,3,49,4)


if __name__=='__main__':
    unittest.main()
