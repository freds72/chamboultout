import os
import re
import io
import math
import logging
import argparse

def make_m3(x=None,y=None,z=None):
    return [
		x or 1,0,0,0,
		0,y or 1,0,0,
		0,0,z or 1,0,
		0,0,0,1]

def m_scale(m,scale):
    m=list([v*scale for v in m])
    m[15]=1
    return m

# generic matrix inverse
def m3_inv(me):
	te=[ me[10]*me[5]-me[6]*me[9], me[10]*me[1]+me[2]*me[9], me[6]*me[1]-me[2]*me[5],0,
		-me[10]*me[4]+me[6]*me[8], me[10]*me[0]-me[2]*me[8],-me[6]*me[0]+me[2]*me[4],0,
		 me[10]*me[4]-me[5]*me[9],-me[9]* me[0]+me[1]*me[8], me[5]*me[0]-me[1]*me[4],0,
		0,0,0,1]
	det = me[0]*te[0]+me[1]*te[4]+me[2]*te[8]
	assert(det>0)
	# not inversible?
	return m_scale(te,1/det)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--x", required=True, type=float, help="X extent")
    parser.add_argument("--y", required=True, type=float, help="Y extent")
    parser.add_argument("--z", required=True ,type=float, help="Z extent")
    parser.add_argument("--density", required=True, type=float, help="Density")    

    args = parser.parse_args()

    ex,ey,ez=args.x,args.y,args.z
    # 4=square(2*extents)
    size = [4*ex*ex,4*ey*ey,4*ez*ez]
    ibody = make_m3(size[1]+size[2],size[0]+size[2],size[0]+size[1])
    # 8=2*2*2 extents
    mass = 8*args.density*(ex*ey*ez)
    ibody = m_scale(ibody,mass/12)
    # invert 
    print(m3_inv(ibody))
    print("mass:{}".format(mass))

if __name__ == '__main__':
    main()