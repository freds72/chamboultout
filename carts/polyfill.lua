pico-8 cartridge // http://www.pico-8.com
version 18
__lua__
-- polygon edge renderer
function polyfill(p,col)
	color(col)
	local p0,nodes=p[#p],{}
	local x0,y0=p0.x,p0.y

	for i=1,#p do
		local p1=p[i]
		local x1,y1=p1.x,p1.y
		local _x1,_y1=x1,y1
		if(y0>y1) x0,y0,x1,y1=x1,y1,x0,y0
		local cy0,cy1,dx=y0\1+1,y1\1,(x1-x0)/(y1-y0)
		if(y0<0) x0-=y0*dx y0=0
	   	x0+=(-y0+cy0)*dx
		for y=cy0,min(cy1,127) do
			local x=nodes[y]
			if x then
				local x,x0=x,x0
				if(x0>x) x,x0=x0,x
				rectfill(x0+1,y,x,y,col)
			else
			 nodes[y]=x0
			end
			x0+=dx					
		end			
		--break
		x0,y0=_x1,_y1
	end
end

function polyline(p,c)	
	-- outline
	color(c)
	local p0=p[#p]
	local x0,y0=p0.x,p0.y
	for i=1,#p do
		local p1=p[i]
		local x1,y1=p1.x,p1.y
		line(x0+0.5,y0+0.5,x1+0.5,y1+0.5)
		x0,y0=x1,y1
	end
end

function tpoly(v,uv)
	local nv,spans=#v,{}
	-- ipairs is slower for small arrays
	for i=1,#v do
		local p0,uv0,p1,uv1=v[i%nv+1],uv[i%nv+1],v[i],uv[i]
		local x0,y0,u0,v0,x1,y1,u1,v1=p0.x,p0.y,uv0[1],uv0[2],p1.x,p1.y,uv1[1],uv1[2]
		if(y0>y1) x0,y0,x1,y1,u0,v0,u1,v1=x1,y1,x0,y0,u1,v1,u0,v0
		local dy=y1-y0
		local dx,du,dv=(x1-x0)/dy,(u1-u0)/dy,(v1-v0)/dy
		local cy0=y0\1+1
		if(y0<0) x0-=y0*dx u0-=y0*du v0-=y0*dv y0=0 cy0=0
		-- sub-pix shift
		local sy=cy0-y0
		x0+=sy*dx
		u0+=sy*du
		v0+=sy*dv
		if(y1>127) y1=127
		for y=cy0,y1 do
			local span=spans[y]
			if span then
				--rectfill(x[1],y,x0,y,offset/16)
				
				local a,au,av,b,bu,bv=x0,u0,v0,unpack(span)
				if(a>b) a,au,av,b,bu,bv=b,bu,bv,a,au,av
				local ca,cb=a\1+1,b\1
				if ca<=cb then
					-- pixel perfect sampling
					local sa,dab=ca-a,b-a
					local dau,dav=(bu-au)/dab,(bv-av)/dab
					tline(ca,y,cb,y,au+sa*dau,av+sa*dav,dau,dav)
				end
			else
				spans[y]={x0,u0,v0}
			end
			x0+=dx
			u0+=du
			v0+=dv
		end
	end
end