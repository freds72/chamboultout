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
				rectfill(x0,y,x,y)
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