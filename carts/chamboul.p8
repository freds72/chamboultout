pico-8 cartridge // http://www.pico-8.com
version 33
__lua__
-- chamboultout
-- by @freds72
-- physic code by: Randy Gaul
-- https://github.com/RandyGaul/qu3e

#include polyfill.lua
#include math.lua

local time_t,time_dt=0,1/30
local _things={}
local physic_actors={}
local v_grav={0,-1,0}
local _sun_dir={0,-0.707,0.707}
local world={}

-- camera
local _cam
local k_far,k_near=0,2
local k_right,k_left=4,8
local z_near=1

-- physic thresholds
local k_small,k_small_v=0.01,0.1
-- baumgarte
local k_bias=0.2
local k_slop=0.05

-->8
-- physic engine
function hitscan(boxes,a,b)
	local closest_hit,closest_t
	for _,box in pairs(boxes) do
		local m=box.m
		-- convert start/end into object space
		local aa,bb=transform_inv(m,a),transform_inv(m,b)
		-- use local space for distance check
		local dir=make_v(aa,bb)
		-- reset starting points for the next convex space
		local p0,p1,hit=aa,bb
		for _,face in pairs(box.model.f) do
			local plane_dist=face.dist
			local dist,otherdist=v_dot(face.n,p0),v_dot(face.n,p1)
			local side,otherside=dist>plane_dist,otherdist>plane_dist
			-- outside of convex space
			if(side and otherside) hit=nil break
			-- crossing a plane
			local t=dist-plane_dist
			if t<0 then
				t-=0x0.01
			else
				t+=0x0.01
			end  
			-- cliping fraction
			local frac=t/(dist-otherdist)
			if frac>0 and frac<1 then
				local p=v_lerp(p0,p1,frac)
				if side then
					-- segment entering
					p0=p
					hit=p0
					hit.owner=box
					hit.face=face
				else
					-- segment leaving
					p1=p
				end
			end
		end
		if hit then
			-- project hit back on segment to find closest hit
			local t=v_dot(dir,hit)
			if closest_hit then
				if(t<closest_t) closest_hit,closest_t=hit,t
			else
				closest_hit,closest_t=hit,t
			end
		end
	end
	-- return hit
	return closest_hit
end


function get_support(vertices,n)
	local dmax,vmax=-32000
	for _,v in pairs(vertices) do
		-- !! invert normal !!
		local d=-v_dot(v,n)
		if d>dmax then
			dmax=d
			vmax=v
		end
	end
	return vmax
end

function query_face_directions(a,b)
	local ma,mb=a.m,b.m
	-- B rotation in A space
	local tx=m_x_m(
		m3_transpose(a.m),{
		1,0,0,0,
		0,1,0,0,
		0,0,1,0,
		-a.pos[1],-a.pos[2],-a.pos[3],1})
	tx=m_x_m(tx,b.m)

	--local tx=m3_x_m3(m3_transpose(ma),b.m)
	--m_set_pos(tx,make_v(a.pos,b.pos))
	-- cache B vertices
	local vb={}
	for i,v in pairs(b.model.v) do
		vb[i]=transform(tx,v)
	end

	local dmax,fmax=-32000
	for _,f in pairs(a.model.f) do
		-- find face in B most opposed to current face
		local v=get_support(vb,f.n)
		local d=v_dot(f.n,v)-f.dist
		if d>dmax then
			dmax=d
			fmax=f
		end
	end
	return dmax,fmax
end

function is_minkowski_face(a,b,c,d)
	local bxa,dxc=v_cross(b,a),v_cross(d,c)
	local cba,dba,adc,bdc=v_dot(c,bxa),v_dot(d,bxa),v_dot(a,dxc),v_dot(b,dxc)
	return cba*dba<0 and adc*bdc<0 and cba*bdc>0
end

function build_minkowski_face(ea,eb,tx)
	local bn1,bn2=rotate(tx,eb.normals[1].n),rotate(tx,eb.normals[2].n)
	v_scale(bn1,-1)
	v_scale(bn2,-1)
	return is_minkowski_face(ea.normals[1].n,ea.normals[2].n,bn1,bn2)
end

function find_edge_closest_points(p1,q1,p2,q2)	
	local s,t=0,0
	local p1,q1,p2,q2=v_clone(p1),v_clone(q1),v_clone(p2),v_clone(q2)
	-- avoid overflow
	v_scale(p1,1/16)
	v_scale(q1,1/16)
	v_scale(p2,1/16)
	v_scale(q2,1/16)
	local d1,d2=make_v(p1,q1),make_v(p2,q2)
	local r=make_v(p1,p2)
	local a=v_dot(d1,d1)
	local e=v_dot(d2,d2)
	local f=v_dot(d2,r)
	local c=v_dot(d1,r)
	local b=v_dot(d1,d2)
	local denom=a*e-b*b
	local s=(b*f-c*e)/denom
	local t=(b*s+f)/e

	local c1,c2=v_add(p1,d1,-s),v_add(p2,d2,-t)
	v_scale(c1,16)
	v_scale(c2,16)
	return c1,c2
end

function query_edge_direction(a,b)
	-- local ma,mb=a.m,b.m
	-- B rotation in A space
	--local tx=m3_x_m3(m3_transpose(ma),b.m)
	--m_set_pos(tx,make_v(a.pos,b.pos))
	--
	local tx=m_x_m(
		m3_transpose(a.m),{
		1,0,0,0,
		0,1,0,0,
		0,0,1,0,
		-a.pos[1],-a.pos[2],-a.pos[3],1})
	tx=m_x_m(tx,b.m)
	-- cache B vertices
	-- local vb={}
	-- for i,v in pairs(b.model.v) do
	-- 	vb[i]=transform(tx,v)
	-- end

	local averts,bverts=a.model.v,b.model.v
	local dmax,closest_pair=-32000,{}
	for _,ea in pairs(a.model.e) do
		local eahead=averts[ea.head]
		for _,eb in pairs(b.model.e) do	
			local ebdir=rotate(tx,eb.direction)
			-- parallel edges?
			if(abs(v_dot(ea.direction,ebdir))>0.99) goto parallel

			-- intersection = minkowski face
			if build_minkowski_face(ea,eb,tx) then
				local axis=v_normz(v_cross(ea.direction,ebdir))
				-- a origin is 0
				if v_dot(axis,eahead)<0 then
					v_scale(axis,-1)
				end
				local ebhead=transform(tx,bverts[eb.head])
				local d=v_dot(axis,make_v(eahead,ebhead))
				if d>dmax then
					dmax=d
					closest_pair.dist=d
					closest_pair.ea=ea
					closest_pair.eb=eb

					-- find closest point
					local c1,c2=find_edge_closest_points(
						eahead,averts[ea.tail],
						ebhead,transform(tx,bverts[eb.tail]))
					closest_pair.c1=c1
					closest_pair.c2=c2
					closest_pair.n=axis
					--
					-- draw_edge(
					-- 	transform(a.m,averts[ea.head]),
					-- 	transform(a.m,averts[ea.tail]),7)
					-- local b0,b1=bverts[eb.head],bverts[eb.tail]
					-- -- local ab=make_v(a.pos,b.pos)
					-- -- b world space rotation
					-- -- rebase pos to a
					-- --b0,b1=
					-- --	v_add(rotate(b.m,b0),ab),
					-- --	v_add(rotate(b.m,b1),ab)
					-- ---- position in A space
					-- --b0,b1=
					-- --	rotate_inv(a.m,b0),
					-- --	rotate_inv(a.m,b1),
					-- --draw_edge(
					-- --	transform(a.m,transform(a.m,b0)),
					-- --	transform(a.m,transform(a.m,b1)),11)
					-- draw_edge(
					-- 	transform(a.m,transform(tx,b0)),
					-- 	transform(a.m,transform(tx,b1)),11)
					-- flip()
				end
			end			
			
			--[[
			local axis=v_normz(v_cross(ea.direction,ebdir))
			local eahead=averts[ea.head]
			-- a origin is 0
			if v_dot(axis,eahead)<0 then
				v_scale(axis,-1)
			end
			-- plane a
			local adist=v_dot(ea.direction,eahead)
			local v=get_support(vb,axis) -- -1 in function
			local d=v_dot(axis,v)-adist
			if d>dmax then
				dmax=d
				eamax=ea
				ebmax=eb
			end
			]]
::parallel::			
		end
	end
	return dmax,closest_pair
end

-- http://media.steampowered.com/apps/valve/2015/DirkGregorius_Contacts.pdf
-- https://www.gdcvault.com/play/1017646/Physics-for-Game-Programmers-The
function overlap(a,b,out)
	local adist,aface=query_face_directions(a,b)
	if(adist>0) return
	local bdist,bface=query_face_directions(b,a)
	if(bdist>0) return

	local edist,closest_edges=query_edge_direction(a,b)
	if(edist>0) return

	-- printh(tostr(time()).."\t faces: "..adist.." "..bdist.." edge:"..edist)
	local contacts={}
	out.contacts=contacts
	if 0.95*edist>max(adist,bdist)+0.01 then
		--printh(tostr(time()).."\t edge contact")
		local ea,eb=closest_edges.ea,closest_edges.eb
		out.edges={ea,eb}	
		out.reference=a
		out.incident=b
		out.n=closest_edges.n
		local c=v_add(closest_edges.c1,closest_edges.c2)
		v_scale(c,0.5)
		add(contacts,c)			
		-- transform edge in world space
		-- debug
		draw_edge(
			transform(a.m,a.model.v[ea.head]),
			transform(a.m,a.model.v[ea.tail]),11)
		draw_edge(
			transform(b.m,b.model.v[eb.head]),
			transform(b.m,b.model.v[eb.tail]),8)
	else
		if 0.95*bdist > adist+0.01 then
			--printh(tostr(time()).."\t face B contact")
			out.reference=b
			out.incident=a
			out.reference_face=bface
			out.flip=true
			out.n=bface.n	
		else
			--printh(tostr(time()).."\t face A contact")
			out.reference=a
			out.incident=b
			out.reference_face=aface	
			out.n=aface.n
		end
		-- find incident face
		local n=rotate(out.reference.m,out.reference_face.n)
		out.incident_face=out.incident:incident_face(n)
		-- clip incident with reference sides
		local tx=m_x_m(
			m3_transpose(out.reference.m),{
			1,0,0,0,
			0,1,0,0,
			0,0,1,0,
			-out.reference.pos[1],-out.reference.pos[2],-out.reference.pos[3],1})
		tx=m_x_m(tx,out.incident.m)
		-- convert incident face into reference space
		for i=1,4 do
			add(contacts,transform(tx,out.incident_face[i]))
		end
		for _,side in pairs(out.reference_face.sides) do
			contacts=axis_poly_clip(
				side.axis,
				side.sign*side.dist,
				contacts,
				-side.sign)	
		end
		-- keep only points under the reference plane
		local side=out.reference_face
		for i=#contacts,1,-1 do
			local v=contacts[i]
			local dist=v_dot(side.n,v)-side.dist
			if dist<0 then
				v.dist=dist
			else
				-- invalid contact
				deli(contacts,i)
			end
		end
	end
	---- draw contacts
	fillp()
	for _,v in pairs(contacts) do
		local x0,y0,w0=_cam:project2d(transform(out.reference.m,v))
		circfill(x0,y0,1,7)

		local n=v_add(v,out.n,4)
		local x1,y1,w1=_cam:project2d(transform(out.reference.m,n))
		line(x0,y0,x1,y1,5)
	end
	flip()

	return true
end

-- creates a collision solver for:
-- body
-- normal
-- body contact point (world position)
-- penetration
function is_contact(a,p,n,d)
	local padot=a:pt_velocity(p)
	local vrel=v_dot(n,padot)
	-- resting condition?
	if(d<k_small and vrel>-k_small_v) return
 return true
end
function make_contact_solver(a,p,n,d)
	-- does nothing
	if(not is_contact(a,p,n,d)) return
	local nimpulse=0
	local ra=make_v(a.pos,p)
	local racn=v_cross(ra,n)

	local nm=a.mass_inv
	nm+=v_dot(racn,rotate(a.i_inv,racn))
	nm=1/nm
	
	-- baumgarte
	local bias=-k_bias*max(d+k_slop)/time_dt

	-- restitution bias
	local dv=-v_dot(v_add(a.v,v_cross(a.omega,ra)),n)
	-- todo:find out unit??
	if dv<-1 then
		bias-=a.hardness*dv
	end
	
	-- contact solver
	return function()
		local dv,n=v_add(a.v,v_cross(a.omega,ra)),v_clone(n)

		local lambda=-nm*(v_dot(dv,n)+bias)
	
		local tempn,nimpulse=nimpulse,max(nimpulse+lambda)
		lambda=nimpulse-tempn
		
		-- impulse too small?
		if(lambda<k_small) return false
		-- correct linear velocity
		v_scale(n,lambda)
		a.v=v_add(a.v,n,a.mass_inv)
		-- correct angular velocity
		a.omega=v_add(
			a.omega,
			rotate(
				a.i_inv,
				v_cross(ra,n)
			))
		return true
	end
end

-- rigid body extension for a given actor
-- bounding box
function make_rigidbody(a)
	local bbox=a.model
	local force,torque=v_zero(),v_zero()
	
	-- compute inertia tensor
	local size=v_clone(a.extents)
	v_scale(size,2)
	size=v_sqr(size)
	local ibody=make_m3(size[2]+size[3],size[1]+size[3],size[1]+size[2])
	m_scale(ibody,a.mass/12)
	
	-- invert 
	local ibody_inv=m3_inv(ibody)
	-- 
	local g={0,-24*a.mass,0}
	local rb={
		i_inv=make_m3(),
		v=v_zero(),
		m=a.m,
		omega=v_zero(),
		mass_inv=1/a.mass,
		-- obj to world space
		pt_toworld=function(self,p)
			return transform(self.m,p)
		end,		
		-- world velocity
		pt_velocity=function(self,p)
			return v_add(v_cross(self.omega,make_v(self.pos,p)),self.v)
		end,
		incident_face=function(self,rn)
			-- world to local (normal)
			rn=rotate_inv(self.m,rn)
			local dmin,fmin,nmin=32000
			for _,f in pairs(bbox.f) do
				local n=f.n
				local d=v_dot(rn,n)
				if d<dmin then
					dmin,fmin,nmin=d,f,n
				end
			end
			return fmin,nmin
		end,
			-- register a force
		add_force=function(self,f,p)
			force=v_add(force,f,a.mass)
			torque=v_add(torque,v_cross(make_v(self.pos,p),f))
		end,
		add_impulse=function(self,f,p)		 
			self.v=v_add(self.v,f,self.mass_inv)
			self.omega=v_add(self.omega,rotate(self.i_inv,v_cross(make_v(self.pos,p),f)))
		end,
		-- apply forces & torque for iteration
		prepare=function(self,dt)
			-- add gravity
			force=v_add(force,g)
		
			-- inverse inertia tensor
			self.i_inv=m3_x_m3(m3_x_m3(self.m,ibody_inv),m3_transpose(self.m))
	
			-- velocity
			self.v=v_add(self.v,force,self.mass_inv*dt)
	
			-- angular velocity
			self.omega=v_add(self.omega,rotate(self.i_inv,torque),dt)
			
			-- friction
			v_scale(self.v,1/(1+dt*0.4))
			v_scale(self.omega,1/(1+dt*0.6))
		end,
		integrate=function(self,dt)
			self.pos=v_add(self.pos,self.v,dt)
			q_dydt(self.q,self.omega,dt)
			self.m=m_from_q(self.q)
			--
			m_set_pos(self.m,self.pos)

			-- clear forces
			force,torque=v_zero(),v_zero()
		end,
		update_contacts=function(self,contacts)
			-- ground contacts against incident face
			local f=self:incident_face(v_up)
			for vi=1,4 do
				local v=f[vi]				
				-- to world space
				local p=self:pt_toworld(v)
				local h,n=0,{0,1,0}
				local depth=h-p[2]
				if depth>k_small then
					depth=v_dot(n,{0,depth,0})
					-- deep enough?
					if depth>-k_small then
						local ct=make_contact_solver(self,p,n,depth)
						if ct then
							add(contacts,ct)
							-- record contact time
							v.contact_t=time_t
							v.n=n
						end
					end
				end
			end
		end
	}
	
	-- register rigid bodies
	return add(physic_actors,setmetatable(a,{__index=rb}))
end

-- physic world
function world:update()
	local contacts={}
	for _,a in pairs(physic_actors) do
		-- collect contacts
		a:update_contacts(contacts)
		a:prepare(time_dt)
	end
	
	-- solve contacts
	for _,c in pairs(contacts) do
		-- multiple iterations
		-- required to fix deep contacts
		for i=1,5 do
			if(c()==false) break
		end
	end
	
	-- move bodies
	for _,a in pairs(physic_actors) do
		a:integrate(time_dt)
	end
	_contacts=contacts
end

-->8
-- 3d engine
-- sort
-- https://github.com/morgan3d/misc/tree/master/p8sort
--
function sort(data)
	local n = #data
	if(n<2) return

	-- form a max heap
	for i = n\2+1, 1, -1 do
	 -- m is the index of the max child
	 local parent, value, m = i, data[i], i + i
	 local key = value.key

	 while m <= n do
	  -- find the max child
	  if ((m < n) and (data[m + 1].key > data[m].key)) m += 1
	  local mval = data[m]
	  if (key > mval.key) break
	  data[parent] = mval
	  parent = m
	  m += m
	 end
	 data[parent] = value
	end

	-- read out the values,
	-- restoring the heap property
	-- after each step
	for i = n, 2, -1 do
	 -- swap root with last
	 local value = data[i]
	 data[i], data[1] = data[1], value

	 -- restore the heap
	 local parent, terminate, m = 1, i - 1, 2
	 local key = value.key

	 while m <= terminate do
	  local mval = data[m]
	  local mkey = mval.key
	  if (m < terminate) and (data[m + 1].key > mkey) then
	   m += 1
	   mval = data[m]
	   mkey = mval.key
	  end
	  if (key > mkey) break
	  data[parent] = mval
	  parent = m
	  m += m
	 end

	 data[parent] = value
	end
end


-->8
-- tracking camera
function make_cam(pos)
	local up={0,1,0}
  	local angle,dangle,velocity={0,0,0},{0,0,0},{0,0,0,}

	-- 
	return {
		pos=v_clone(pos),    
		update=function(self)
			-- damping      
			angle[3]*=0.8
			v_scale(dangle,0.6)
			v_scale(velocity,0.7)

			-- move
			local dx,dz,a,jmp=0,0,angle[2],0
			if(btn(0,1)) dx=2
			if(btn(1,1)) dx=-2
			if(btn(2,1)) dz=2
			if(btn(3,1)) dz=-2

			dangle=v_add(dangle,{stat(39),stat(38),dx/4})
			angle=v_add(angle,dangle,1/1024)
			
			local c,s=cos(a),-sin(a)
			velocity=v_add(velocity,{s*dz-c*dx,0,c*dz+s*dx}) 	
			
			local pos=v_add(self.pos,velocity)

			-- update rotation
			local m=make_m_from_euler(unpack(angle))	
			-- inverse view matrix
            m[2],m[5]=m[5],m[2]
            m[3],m[9]=m[9],m[3]
            m[7],m[10]=m[10],m[7]
            --
            self.m=m_x_m(m,{
				1,0,0,0,
				0,1,0,0,
				0,0,1,0,
				-pos[1],-pos[2],-pos[3],1
			})
            self.pos=pos
		end,
		project2d=function(self,p)
			p=transform(self.m,p)
			if p[3]>z_near then
				local w=64/p[3]
				return 64+p[1]*w,64-p[2]*w,w
			end
		end
	}
end

function axis_poly_clip(axis,dist,v,sign)
	sign=sign or 1
	local res,v0={},v[#v]
	local d0=sign*(v0[axis]-dist)
	for i=1,#v do
		local v1=v[i]
		local d1=sign*(v1[axis]-dist)
		if d1>0 then
			if d0<=0 then
				local nv=v_lerp(v0,v1,d0/(d0-d1))
				-- "fixes" clipping
				nv[axis]=dist
				res[#res+1]=nv
			end
			res[#res+1]=v1
		elseif d0>0 then
			local nv=v_lerp(v0,v1,d0/(d0-d1))
			-- "fixes" clipping
			nv[axis]=dist
			res[#res+1]=nv
		end
		v0=v1
		d0=d1
	end
	return res
end

-- vertex cache class
-- uses m (matrix) and v (vertices) from self
-- saves the 'if not ...' in inner loop
local v_cache_cls={
	-- v is vertex reference
	__index=function(t,v)
		-- inline: local a=m_x_v(t.m,t.v[k])
		local m,x,y,z=t.m,v[1],v[2],v[3]
		local ax,ay,az=m[1]*x+m[5]*y+m[9]*z+m[13],m[2]*x+m[6]*y+m[10]*z+m[14],m[3]*x+m[7]*y+m[11]*z+m[15]

		local outcode=k_near
		if(az>z_near) outcode=k_far
		if(ax>az) outcode+=k_right
		if(-ax>az) outcode+=k_left

		-- not faster :/
		-- local bo=-(((az-z_near)>>31)<<17)-(((az-ax)>>31)<<18)-(((az+ax)>>31)<<19)
		-- assert(bo==outcode,"outcode:"..outcode.." bits:"..bo)

		-- assume vertex is visible, compute 2d coords
		local w=64/az
		local a={ax,ay,az,outcode=outcode,x=64+ax*w,y=64-ay*w,w=w}
		t[v]=a
		return a
	end
}

function collect_faces(model,m,out)
	-- cam pos in object space
	local cam_pos=transform_inv(m,_cam.pos)
	-- sun vector in model space
	local sun=rotate_inv(m,_sun_dir)

	-- object to world
	-- world to cam
	-- vertex cache (and model context)
	local v_cache=setmetatable({m=m_x_m(_cam.m,m)},v_cache_cls)

	for _,face in pairs(model.f) do
		-- if v_dot(face.n,cam_pos)>face.dist then
			-- project vertices (always 4!!)
			local v0,v1,v2,v3=v_cache[face[1]],v_cache[face[2]],v_cache[face[3]],v_cache[face[4]]
			-- mix of near/far verts?
			if v0.outcode&v1.outcode&v2.outcode&v3.outcode==0 then
				local verts={v0,v1,v2,v3}
				-- mix of near+far vertices?
				if (v0.outcode|v1.outcode|v2.outcode|v3.outcode)&2!=0 then
					verts=axis_poly_clip(3,z_near,verts)
					-- project
					for _,v in pairs(verts) do
						local w=64/v[3]
						v.x=64+v[1]*w
						v.y=64-v[2]*w
					end
				end
				if #verts>2 then
					verts.face=face
					verts.light=mid(-v_dot(sun,face.n),0,1)
					-- sort key
					-- todo: improve
					verts.key=(v0.w+v1.w+v2.w+v3.w)/4
					verts.visible=v_dot(face.n,cam_pos)>face.dist
					out[#out+1]=verts
				end
			end
		--end
::skip::
	end
end

-- draw face
function draw_faces(faces,hit)
	for i,d in ipairs(faces) do
		-- todo: color ramp	
		fillp()
		if(not d.visible) fillp(0xa5a5.8)
		if(hit and hit.reference_face==d.face) polyfill(d,11)		
		if(hit and hit.incident_face==d.face) polyfill(d,8)		
		-- polyfill(d,c)		
		polyline(d,1)
	end
end

function draw_ground()
    local out={}
	local m={
		1,0,0,0,
		0,1,0,0,
		0,0,1,0,
		0,0,0,1
	}
	m_set_pos(m,{_cam.pos[1],-0.5,_cam.pos[3]})
	collect_faces(_ground.model,m,out)

    draw_faces(out)
end

function make_box(mass,extents,pos,q)
	local ex,ey,ez=unpack(extents)
	ex/=2
	ey/=2
	ez/=2
	local verts={
			split"-1,-1,-1",
			split"1,-1,-1",
			split"1,-1,1",
			split"-1,-1,1",
			split"-1,1,-1",
			split"1, 1,-1",
			split"1, 1,1",
			split"-1, 1,1",
		}
	local faces={	
			-- edges + normal axis direction (- to indicate sign)		
			split"4,3,2,1,-2",
			split"1,2,6,5,-3",
			split"2,3,7,6,1",
			split"3,4,8,7,3",
			split"4,1,5,8,-1",
			split"5,6,7,8,2"
		}
	local model={
		v=verts,
		-- faces
		f=faces,
		e={
			-- bottom loop
			{tail=1,head=2,direction={1,0,0} ,normals={faces[1],faces[2]}},
			{tail=2,head=3,direction={0,0,1} ,normals={faces[1],faces[3]}},
			{tail=3,head=4,direction={-1,0,0},normals={faces[1],faces[4]}},
			{tail=4,head=1,direction={0,0,-1},normals={faces[1],faces[5]}},
			-- support edges
			{tail=1,head=5,direction=v_up,normals={faces[2],faces[5]}},
			{tail=2,head=6,direction=v_up,normals={faces[3],faces[2]}},
			{tail=3,head=7,direction=v_up,normals={faces[4],faces[3]}},
			{tail=4,head=8,direction=v_up,normals={faces[5],faces[4]}},
			-- top loop
			{tail=5,head=6,direction={1,0,0} ,normals={faces[2],faces[6]}},
			{tail=6,head=7,direction={0,0,1} ,normals={faces[3],faces[6]}},
			{tail=7,head=8,direction={-1,0,0},normals={faces[4],faces[6]}},
			{tail=8,head=5,direction={0,0,-1},normals={faces[5],faces[6]}}
		}
	}
	for _,v in pairs(verts) do
		v[1]*=ex
		v[2]*=ey
		v[3]*=ez
	end
	
	for _,f in pairs(faces) do
		-- de-reference vertex indices
		for i=1,4 do
			f[i]=verts[f[i]]
		end
		-- index (and sign of )
		local axis=deli(f,5)
		f.axis=abs(axis)
		f.sign=sgn(axis)
		-- find sides
		local sides={}
		for _,e in pairs(model.e) do
			if(e.normals[1]==f) add(sides,e.normals[2])
			if(e.normals[2]==f) add(sides,e.normals[1])
		end
		f.sides=sides
		-- normal
		f.n=v_normz(
				v_cross(
					make_v(f[1],f[4]),
					make_v(f[1],f[2])))
		-- fast viz check
		f.dist=v_dot(f.n,f[1])
	end
	-- initial condition
	local m=m_from_q(q)
	m_set_pos(m,pos)

	return {
		mass=mass,
		hardness=0.1,
		extents={ex,ey,ez},
		model=model,
		pos=v_clone(pos),
		q=q_clone(q),
		m=m
	}
end

function make_picker()
	local lmb=0
	return {
		update=function(self)			
		end
	}
end

-->8
-- game loop
function _init()
	-- capture mouse
	-- enable lock+button alias
	poke(0x5f2d,7)

	_cam=make_cam({0,8,-40})

	-- cube
	--add(_things,
	--	make_rigidbody(
	--		make_box(
	--			1,{5,5,5},
	--			{0,50,0},make_q(v_normz({rnd(),rnd(),rnd()},rnd())))))
--
	_a_box=make_rigidbody(make_box(
		1,{5,5,5},
		{6,3,0},
		--make_q(v_normz({rnd(),rnd(),rnd()},rnd()))
		make_q(v_up,0.125)
	))
	_b_box=make_rigidbody(make_box(
		1,{10,5,10},
		{0,0,0},
		make_q(v_up,0.125)
		--make_q(v_normz({rnd(),rnd(),rnd()},rnd()))
		--q_x_q(
		--	make_q({1,0,0},0.125),
		--	make_q({0,1,0},0.125))
	))
	add(_things,_a_box)
	add(_things,_b_box)

	-- floor
	_ground=make_box(0,{500,1,500},{0,-0.5,0},make_q(v_up,0))
end

function _update()
	_cam:update()

	-- update "test box"
	-- local m=_cam.m
	-- _incident_box.pos=v_add(_cam.pos,{m[3],m[7],m[11]},35)
	-- _incident_box.m=m3_transpose({unpack(m)})
	-- m_set_pos(_incident_box.m,_incident_box.pos)

	local rot_axis=v_normz({1,1,0})	
	-- local m=m_from_q(make_q(v_up,time()/8))
	-- _b_box.pos={0,10*cos(time()/16),0}
	-- m_set_pos(m,_b_box.pos)
	--_b_box.m=m
-- 
	local m=m_from_q(
		q_x_q(
			make_q(rot_axis,time()/32),
			make_q(v_up,time()/16)))
	local m=m_from_q(make_q({0,0,1},time()/16))
	-- local m=_a_box.m
	_a_box.pos={7,5*cos(time()/16),0}
	m_set_pos(m,_a_box.pos)
	_a_box.m=m

    --world:update()
	
	time_t+=1
end

function draw_edge(a,b,c)
	local x0,y0,w0=_cam:project2d(a)
	local x1,y1,w1=_cam:project2d(b)
	if w0 and w1 then
		line(x0,y0,x1,y1,c)
	end
end

function _draw()
    cls()
	draw_ground()

    local out={}
	for _,thing in pairs(_things) do
		collect_faces(thing.model,thing.m,out)
	end

	sort(out)

	local ohit={}
	if overlap(_a_box,_b_box,ohit) then
		print("touch: "..(ohit.edges and "edges" or "faces"),2,2,8)
	end
    draw_faces(out,ohit)
end

