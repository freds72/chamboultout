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
		-- !! invert normal !!
	local axis,sign,dmax,vmax=n.axis,-n.sign,-32000
	for _,v in pairs(vertices) do
		-- faster v_dot(n,v)
		local d=sign*v[axis]
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

	-- cache B vertices
	local vb={}
	for i,v in pairs(b.model.v) do
		vb[i]=transform(tx,v)
	end

	local dmax,fmax=-32000
	for _,f in pairs(a.model.f) do
		-- find vertex in B most "included" in current face
		local v=get_support(vb,f)
		-- faster v_dot(f.n,v)
		local d=f.sign*v[f.axis]-f.dist
		-- early exit
		if(d>0) return d
		if d>dmax then
			dmax=d
			fmax=f
		end
	end
	return dmax,fmax
end


function is_minkowski_face(a,b,c,d)
	local bxa,dxc=v_cross(b.n,a.n),v_cross(d,c)
	local cba,dba,adc,bdc=v_dot(c,bxa),v_dot(d,bxa),a.sign*dxc[a.axis],b.sign*dxc[b.axis]
	return cba*dba<0 and adc*bdc<0 and cba*bdc>0
end

function build_minkowski_face(ea,eb,tx)
	local n1,n2=eb.normals[1],eb.normals[2]
	--v_scale(bn1,-1)
	--v_scale(bn2,-1)
	return is_minkowski_face(
		ea.normals[1],ea.normals[2],
		rotate_axis(tx,n1.axis,-n1.sign),rotate_axis(tx,n2.axis,-n2.sign))
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

function rotate_axis(tx,axis,sign)
	axis=(axis-1)<<2
	return {sign*tx[axis+1],sign*tx[axis+2],sign*tx[axis+3]} 
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
		local eadir=ea.direction
		for _,eb in pairs(b.model.e) do	
			local ebdir=eb.direction
			-- optimized rotate(tx,eb.direction)
			ebdir=rotate_axis(tx,ebdir.axis,ebdir.sign)
			-- parallel edges?
			if(abs(ebdir[eadir.axis])>0.99) goto parallel

			-- intersection = minkowski face
			if build_minkowski_face(ea,eb,tx) then
				local axis=v_normz(v_cross(ea.direction,ebdir))
				-- a origin is 0
				if v_dot(axis,eahead)<0 then
					v_scale(axis,-1)
				end
				local ebhead=transform(tx,bverts[eb.head])
				local d=v_dot(axis,make_v(eahead,ebhead))
				-- early exit
				if(d>0) return d
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
-- https://www.randygaul.net/2019/06/19/collision-detection-in-2d-or-3d-some-steps-for-success/
function overlap(a,b)
	-- simplified version for ground/object
	if(a.is_ground) return ground_overlap(a,b)
	if(b.is_ground) return ground_overlap(b,a)
	
	local adist,aface=query_face_directions(a,b)
	if(adist>0) return
	local bdist,bface=query_face_directions(b,a)
	if(bdist>0) return
	
	local edist,closest_edges=query_edge_direction(a,b)
	if(edist>0) return

	-- printh(tostr(time()).."\t faces: "..adist.." "..bdist.." edge:"..edist)
	local out,contacts={},{}
	if 0.95*edist>max(adist,bdist)+0.01 then
		--printh(tostr(time()).."\t edge contact")
		local ea,eb=closest_edges.ea,closest_edges.eb
		out.edges={ea,eb}	
		out.reference=a
		out.incident=b
		out.n=rotate(a.m,closest_edges.n)
		local c=transform(a.m,v_add(closest_edges.c1,closest_edges.c2))
		-- middle point
		v_scale(c,0.5)
		c.dist=closest_edges.dist		
		add(contacts,c)			
		-- transform edge in world space
		-- debug
		--draw_edge(
		--	transform(a.m,a.model.v[ea.head]),
		--	transform(a.m,a.model.v[ea.tail]),11)
		--draw_edge(
		--	transform(b.m,b.model.v[eb.head]),
		--	transform(b.m,b.model.v[eb.tail]),8)
		--	flip()
	else
		if 0.95*bdist > adist+0.01 then
			--printh(tostr(time()).."\t face B contact")
			out.reference=b
			out.incident=a
			out.reference_face=bface
			out.flip=true
			out.n=rotate(b.m,bface.n)
		else
			--printh(tostr(time()).."\t face A contact")
			out.reference=a
			out.incident=b
			out.reference_face=aface	
			out.n=rotate(a.m,aface.n)
			--v_scale(out.n,-1)
		end
		-- find incident face		
		local incident_face=out.incident:incident_face(out.n)
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
			add(contacts,transform(tx,incident_face[i]))
		end
		for _,side in pairs(out.reference_face.sides) do
			if(#contacts==0) break			
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
			-- "deep" enough contact?
			if dist<=0 then				
				v=transform(out.reference.m,v)
				v.dist=dist
				contacts[i]=v
			else
				-- invalid contact
				deli(contacts,i)
			end
		end
	end
	-- draw contacts
	-- fillp()
	-- for _,v in pairs(contacts) do
	-- 	local x0,y0,w0=_cam:project2d(v)
	-- 	circfill(x0,y0,1,7)
--
	-- 	local n=v_add(v,out.n,4)
	-- 	local x1,y1,w1=_cam:project2d(n)
	-- 	line(x0,y0,x1,y1,5)
	-- end
	-- flip()

	out.contacts=contacts
	return out
end

function ground_overlap(a,b)
	-- printh(tostr(time()).."\t faces: "..adist.." "..bdist.." edge:"..edist)
	local out,contacts={
		reference=a,
		incident=b,
		n=v_clone(v_up),
	},{}
	
	-- find incident face
	local incident_face=out.incident:incident_face(v_up)
	-- keep only points under the reference plane
	for i=1,4 do
		local v=transform(b.m,incident_face[i])
		local dist=v[2]
		-- "deep" enough contact?
		if dist<0 then				
			v.dist=dist
			add(contacts,v)
		end
	end
	-- no point below ground
	if(#contacts==0) return
	-- draw contacts
	-- fillp()
	-- for _,v in pairs(contacts) do
	-- 	local x0,y0,w0=_cam:project2d(v)
	-- 	circfill(x0,y0,1,7)
--
	-- 	local n=v_add(v,out.n,4)
	-- 	local x1,y1,w1=_cam:project2d(n)
	-- 	line(x0,y0,x1,y1,5)
	-- end
	-- flip()

	out.contacts=contacts
	return out
end

-- creates a collision solver for:
-- body
-- normal
-- body contact point (world position)
-- penetration
function is_contact(a,p,n,d,sign)
	sign=sign or 1
	local padot=a:pt_velocity(p)
	local vrel=sign*v_dot(n,padot)
	-- resting condition or separating
	if(d<k_small and vrel>-k_small_v) return
	return true
end
function make_contact_solver(a,b,n,p,dist)
	-- valid contact (e.g)
	if(not is_contact(a,p,n,dist,-1) and not is_contact(b,p,n,dist)) return
	local nimpulse=0
	local ra,rb=make_v(a.pos,p),make_v(b.pos,p)
	local racn,rbcn=v_cross(ra,n),v_cross(rb,n)
	
	local nm=a.mass_inv+b.mass_inv
	nm+=v_dot(racn,rotate(a.i_inv,racn))+v_dot(rbcn,rotate(b.i_inv,rbcn))
	nm=1/nm

	-- baumgarte
	local bias=-k_bias*min(dist+k_slop)/time_dt

	-- restitution bias
	local dv=
		v_dot(
			v_add(
				v_add(b.v,v_cross(b.w,rb)),
				v_add(a.v,v_cross(a.w,ra)),
				-1),
			n)
	-- todo:find out unit??
	if dv<-1 then
		bias-=max(a.hardness,b.hardness)*dv
	end
	-- contact solver
	return function()
		local dv=
			v_add(
				v_add(b.v,v_cross(b.w,rb)),
				v_add(a.v,v_cross(a.w,ra)),
				-1)

		local lambda=nm*max(-v_dot(dv,n)+bias)
		
		-- clamp impulse (+overshoot control)
		local tempn=nimpulse
		nimpulse=max(tempn+lambda)
		lambda=nimpulse-tempn			
	
		-- impulse too small?
		if(lambda<k_small) return

		-- correct linear velocity
		local impulse=v_clone(n)
		v_scale(impulse,lambda)
		a.v=v_add(a.v,impulse,-a.mass_inv)
		-- correct angular velocity
		a.w=v_add(
			a.w,
			rotate(
				a.i_inv,
				v_cross(ra,impulse)
			),
			-1)
		b.v=v_add(b.v,impulse,b.mass_inv)
		-- correct angular velocity
		b.w=v_add(
			b.w,
			rotate(
				b.i_inv,
				v_cross(rb,impulse)
			))
		return true
	end
end

-- rigid body extension for a given actor
-- bounding box
function make_rigidbody(a)
	local bbox=a.model
	local force,torque=v_zero(),v_zero()
	local is_static=false

	-- compute (inverse) inertia tensor
	local ibody_inv
	if a.mass>0 then
		local ex,ey,ez=unpack(a.extents)
		local size={ex*ex,ey*ey,ez*ez}
		-- 4=square(2*extents)
		v_scale(size,4)
		local ibody=make_m3(size[2]+size[3],size[1]+size[3],size[1]+size[2])
		-- 8=2*2*2 extents
		local mass=8*a.mass*(ex*ey*ez)*(a.density or 0.1)
		m_scale(ibody,mass/12)
		
		-- invert 
		ibody_inv=m3_inv(ibody)
	else
		is_static=true
		ibody_inv=make_m3(0,0,0)
	end

	-- 
	local g={0,-9.81*a.mass,0}
	local rb={
		i_inv=is_static and make_m3(0,0,0) or make_m3(),
		v=v_zero(),
		m=a.m,
		w=v_zero(),
		mass_inv=is_static and 0 or 1/a.mass,
		-- obj to world space
		pt_toworld=function(self,p)
			return transform(self.m,p)
		end,		
		-- world velocity
		pt_velocity=function(self,p)
			return v_add(v_cross(self.w,make_v(self.pos,p)),self.v)
		end,
		incident_face=function(self,rn)
			-- world to local (normal)
			rn=rotate_inv(self.m,rn)
			local dmin,fmin=32000
			for _,f in pairs(bbox.f) do
				local d=f.sign*rn[f.axis]
				if d<dmin then
					dmin,fmin=d,f
				end
			end
			return fmin
		end,
		-- register a force
		add_force=function(self,f,p)
			if(is_static) return
			self.sleeping=nil
			force=v_add(force,f,a.mass)
			torque=v_add(torque,v_cross(make_v(self.pos,p),f))
		end,
		-- apply forces & torque for iteration
		prepare=function(self,dt)
			if(is_static or self.sleeping) return

			-- add gravity
			force=v_add(force,g)
		
			-- inverse inertia tensor
			self.i_inv=m3_x_m3(m3_x_m3(self.m,ibody_inv),m3_transpose(self.m))
	
			-- velocity
			self.v=v_add(self.v,force,self.mass_inv*dt)
	
			-- angular velocity
			self.w=v_add(self.w,rotate(self.i_inv,torque),dt)
			
			-- friction
			v_scale(self.v,1/(1+dt*0.4))
			v_scale(self.w,1/(1+dt*0.6))
		end,
		integrate=function(self,dt)
			if(is_static or self.sleeping) return

			-- clear forces
			force,torque=v_zero(),v_zero()

			-- no significant velocity/angular v?
			if(v_dot(self.v,self.v)<k_small and v_dot(self.w,self.w)<k_small_v) self.sleeping=true self.v=v_zero() self.w=v_zero() return

			self.pos=v_add(self.pos,self.v,dt)
			q_dydt(self.q,self.w,dt)
			self.m=m_from_q(self.q)
			--
			m_set_pos(self.m,self.pos)
		end
	}
	-- register rigid bodies
	return add(physic_actors,setmetatable(a,{__index=rb}))
end

-- physic world
function world:update()
	local contacts={}
	-- update bodies
	for _,a in pairs(physic_actors) do
		a:prepare(time_dt)
	end

	-- collect manifolds
	for i=1,#physic_actors do
		local a=physic_actors[i]
		for j=i+1,#physic_actors do
			local b=physic_actors[j]
			local m=overlap(a,b)
			if m then
				a.sleeping=nil
				b.sleeping=nil
				for _,p in pairs(m.contacts) do										
					add(contacts,make_contact_solver(m.reference,m.incident,m.n,p,p.dist))
				end
			end
		end
	end

	-- solve manifolds
	-- multiple iterations
	-- required to fix deep contacts
	for j=1,3 do
		for i=#contacts,1,-1 do
			-- still a valid contact?
			if(not contacts[i]()) deli(contacts,i)
		end
	end
	
	-- move bodies
	for _,a in pairs(physic_actors) do
		a:integrate(time_dt)
	end
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

function collect_faces(thing,model,m,out)
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
					verts.thing=thing
					verts.model=model
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
		--if(not d.visible) fillp(0xa5a5.8)
		if(hit and hit.reference_face==d.face) polyfill(d,11)		
		if(hit and hit.incident_face==d.face) polyfill(d,8)		
		if d.visible then
			polyfill(d,d.model.shadeless and d.model.color or (d.model.color+d.light*3))
			polyline(d,d.thing.sleeping and 11 or 5)
		end
		--polyline(d,1)
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
	collect_faces(_ground,_ground.model,m,out)

    draw_faces(out)
end

_color=5
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
		color=_color,
		v=verts,
		-- faces
		f=faces,
		e={
			-- bottom loop
			{tail=1,head=2,direction=1 ,normals={faces[1],faces[2]}},
			{tail=2,head=3,direction=3 ,normals={faces[1],faces[3]}},
			{tail=3,head=4,direction=-1,normals={faces[1],faces[4]}},
			{tail=4,head=1,direction=-3,normals={faces[1],faces[5]}},
			-- support edgessplit
			{tail=1,head=5,direction=2,normals={faces[2],faces[5]}},
			{tail=2,head=6,direction=2,normals={faces[3],faces[2]}},
			{tail=3,head=7,direction=2,normals={faces[4],faces[3]}},
			{tail=4,head=8,direction=2,normals={faces[5],faces[4]}},
			-- top loop
			{tail=5,head=6,direction=1,normals={faces[2],faces[6]}},
			{tail=6,head=7,direction=3,normals={faces[3],faces[6]}},
			{tail=7,head=8,direction=-1,normals={faces[4],faces[6]}},
			{tail=8,head=5,direction=-3,normals={faces[5],faces[6]}}
		}
	}
	--_color+=4
	for _,v in pairs(verts) do
		v[1]*=ex
		v[2]*=ey
		v[3]*=ez
	end
	for i,e in pairs(model.e) do
		local axis=e.direction
		local direction=v_zero()
		direction.axis=abs(axis)
		direction.sign=sgn(axis)
		direction[direction.axis]=direction.sign
		model.e[i].direction=direction
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
		hardness=0.4,
		extents={ex,ey,ez},
		model=model,
		pos=v_clone(pos),
		q=q_clone(q),
		m=m
	}
end

function make_ground()
	local model={
		-- faces
		f={
			{
				axis=2,
				sign=1,
				sides={},
				n={0,1,0},
				dist=0
			}
		},
		e={}
	}
	
	return {
		is_ground=true,
		mass=0,
		hardness=0.2,
		model=model,
		pos=v_zero(),
		q=make_q(v_up,0),
		m=make_m3()
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

	_cam=make_cam({0,8,-20})

	-- cube
	--add(_things,
	--	make_rigidbody(
	--		make_box(
	--			1,{5,5,5},
	--			{0,50,0},make_q(v_normz({rnd(),rnd(),rnd()},rnd())))))
--
	--add(_things,make_rigidbody(make_box(
	--	1,{5,5,5},
	--	{2,18,0},
	--	make_q(v_up,rnd())
	--)))

	make_rigidbody(make_ground())

	add(_things,
		make_rigidbody(make_box(
			1,{2,2,2},
			{0,18,0},
			make_q(v_normz({rnd(),rnd(),rnd()},rnd()))
			--make_q(v_up,rnd())
		))
	)

	_a_box=make_rigidbody(make_box(
		1,{5,2,5},
		{0,15,0},
		make_q(v_normz({rnd(),rnd(),rnd()},rnd()))
		--make_q(v_up,rnd())
	))
	add(_things,_a_box)

	_b_box=make_rigidbody(make_box(
		1,{5,5,5},
		{2,8,0},
		--make_q(v_up,0)
		make_q(v_normz({rnd(),rnd(),rnd()},rnd()))
		--q_x_q(
		--	make_q({1,0,0},0.125),
		--	make_q({0,1,0},0.125))
	))
	
	add(_things,_b_box)

	-- floor
	_ground=make_box(0,{500,1,500},{0,-0.5,0},make_q(v_up,0))
	_ground.model.shadeless=true
	_ground.model.color=6
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
	-- local m=m_from_q(
	-- 	q_x_q(
	-- 		make_q(rot_axis,time()/32),
	-- 		make_q(v_up,time()/16)))
	-- local m=m_from_q(make_q({0,0,1},time()/16))
	-- -- local m=_a_box.m
	-- _a_box.pos={7,5*cos(time()/16),0}
	-- m_set_pos(m,_a_box.pos)
	-- _a_box.m=m
--
    world:update()
	
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
		collect_faces(thing,thing.model,thing.m,out)
	end

	sort(out)

    draw_faces(out)
end

