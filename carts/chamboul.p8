pico-8 cartridge // http://www.pico-8.com
version 33
__lua__
-- chamboultout
-- by @freds72
-- physic code based on Randy Gaul repo:
-- https://github.com/RandyGaul/qu3e

#include polyfill.lua
#include math.lua

-- globals
local _things,_scene={}
local _sun_dir={0,-0.707,0.707}
local _dithers={}

-- camera
local _cam
local k_far,k_near=0,2
local k_right,k_left=4,8
local k_up,k_down=16,32
local z_near=1

-- physic thresholds+baumgarte
local time_dt=1/30
local k_small,k_small_v,k_bias,k_slop=0.01,0.1,0.3,0.05

-->8
-- physic engine
-- http://media.steampowered.com/apps/valve/2015/DirkGregorius_Contacts.pdf
-- https://www.gdcvault.com/play/1017646/Physics-for-Game-Programmers-The
-- https://www.randygaul.net/2019/06/19/collision-detection-in-2d-or-3d-some-steps-for-success/
-- auto filled by make_box :[
local face_by_id={}

function overlap(a,b)
	if(a.static and b.static) return
	-- 
	if(a.disabled or b.disabled) return
	-- simplified version for ground/object
	if(a.is_ground) return ground_overlap(a,b)
	if(b.is_ground) return ground_overlap(b,a)
	
	-- cannot overlap
	if(v_len(make_v(a.pos,b.pos))>a.radius+b.radius) return

	local absc,c={},m3_x_m3(m3_transpose(a.m),b.m)
	for i,v in pairs(c) do
		absc[i]=abs(v)
	end
	-- a->b (world space) to a space
	-- ab in a space
	local ab=make_v(a.pos,b.pos)
	local t=rotate_inv(a.m,ab)
	
	local adist,bdist,edist,aaxis,baxis,closest_solution=-32000,-32000,-32000
	-- a vs b
	for i=1,3 do
		local d=abs(t[i])-(a.extents[i]+v_dot(m_column(absc,i),b.extents))
		-- separating axis
		if(d>0) return		
		if d>adist then
			adist=d
			aaxis=i
		end
	end
	-- b vs a
	for i=1,3 do
		local d=abs(v_dot(t, m_row(c,i)))-(b.extents[i]+v_dot(m_row(absc,i),a.extents))
		-- separating axis
		if(d>0) return	
		if d>bdist then
			bdist=d
			baxis=i
		end
	end

	-- edge query left out: resulting solution was not "strong" enough \るそ/

	-- printh(tostr(time()).."\t faces: "..adist.." "..bdist.." edge:"..edist)
	local out,contacts={},{}
	local rface,tx
	if 0.95*bdist > adist+0.01 then
		--printh(tostr(time()).."\t face B contact")
		out.reference=b
		out.incident=a
		rface=baxis
		out.n=rotate_axis(b.m,baxis,1)	
		-- flipped "frame of reference"
		v_scale(ab,-1)
		-- update basis matrix
		tx=m_x_m(make_inv_transform(b.m,b.pos),a.m)
	else
		--printh(tostr(time()).."\t face A contact")
		out.reference=a
		out.incident=b
		rface=aaxis
		out.n=rotate_axis(a.m,aaxis,1)		
		-- 
		tx=m_x_m(make_inv_transform(a.m,a.pos),b.m)
	end
	if v_dot(out.n,ab)<0 then
		rface=-rface
		-- flip normal to match
		v_scale(out.n,-1)
	end
	local reference_face=out.reference.model.f[face_by_id[rface]]		
	out.reference_face=reference_face
	-- find incident face		
	local incident_face=out.incident:incident_face(out.n)
	out.incident_face=incident_face
	-- clip incident with reference sides
	-- convert incident face into reference space
	for i=1,4 do
		add(contacts,transform(tx,incident_face[i]))
	end
	for _,side in pairs(reference_face.sides) do
		-- for some reason clipping removed all points (should not really happen)
		if(#contacts==0) return			
		contacts=axis_poly_clip(
			side.axis,
			side.sign*side.dist,
			contacts,
			-side.sign)	
	end
	-- keep only points under the reference plane
	local side=reference_face
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
	-- cannot touch ground, fast exit
	if(b.pos[2]>b.radius) return

	-- printh(tostr(time()).."\t faces: "..adist.." "..bdist.." edge:"..edist)
	local out,contacts={
		reference=a,
		incident=b,
		n={0,1,0},
	},{}
	
	-- find incident face
	local m,incident_face=b.m,out.incident:incident_face(v_up)
	-- keep only points under the reference plane
	local m2,m6,m10,m14=m[2],m[6],m[10],m[14]
	for i=1,4 do
		-- to world space
		local v=incident_face[i]
		local y=m2*v[1]+m6*v[2]+m10*v[3]+m14
		-- "deep" enough contact?
		if y<0 then				
			add(contacts,transform(b.m,v)).dist=y
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
	local vrel=(sign or 1)*v_dot(n,a:pt_velocity(p))
	-- resting condition or separating
	if(d<k_small and vrel>-k_small_v) return
	return true
end
function make_contact_solver(a,b,n,p,dist,tangents)
	-- valid contact (e.g)
	if(not is_contact(a,p,n,dist,-1) and not is_contact(b,p,n,dist)) return
	local nimpulse,mass,tm,timpulse,friction,ra,rb=0,a.mass_inv+b.mass_inv,{},{0,0},sqrt(a.friction*b.friction),make_v(a.pos,p),make_v(b.pos,p)
	local racn,rbcn=v_cross(ra,n),v_cross(rb,n)
	-- relative velocity at contact point
	local function rel_vel()
		return 	v_add(
					v_add(b.v,v_cross(b.w,rb)),
					v_add(a.v,v_cross(a.w,ra)),
					-1)
	end

	-- normal mass
	local nm=1/(mass+v_dot(racn,rotate(a.i_inv,racn))+v_dot(rbcn,rotate(b.i_inv,rbcn)))

	-- tangent mass
	for i=1,2 do
		local ract,rbct=v_cross(tangents[i],ra),v_cross(tangents[i],rb)
		tm[i]=1/(mass+v_dot(ract,rotate(a.i_inv,ract))+v_dot(rbct,rotate(b.i_inv,rbct)))
	end

	-- baumgarte
	local bias=-k_bias*min(dist+k_slop)/time_dt

	-- restitution bias
	local dv=v_dot(rel_vel(),n)

	-- todo:find out unit??
	if dv<-1 then
		bias-=max(a.hardness,b.hardness)*dv
	end	

	-- contact solver
	return function()
		local dv=rel_vel()

		-- friction impulse
		for i=1,2 do
			local lambda=-v_dot(dv,tangents[i])*tm[i]

			-- calculate frictional impulse
			local maxlambda=friction*nimpulse

			-- clamp frictional impulse
			local oldpt=timpulse[i]
			timpulse[i]=mid(oldpt+lambda, -maxlambda, maxlambda)
			lambda=timpulse[i]-oldpt

			-- apply friction impulse
			local impulse=v_clone(tangents[i],lambda)
			a:apply_impulse(impulse,ra,-1)
			b:apply_impulse(impulse,rb,1)
		end

		-- normal impulse
		local lambda=nm*max(-v_dot(dv,n)+bias)
		
		-- clamp impulse (+overshoot control)
		local tempn=nimpulse
		nimpulse=max(tempn+lambda)
		lambda=nimpulse-tempn			
	
		-- impulse too small?
		if(lambda<k_small) return

		-- correct linear velocity
		local impulse=v_clone(n,lambda)
		a:apply_impulse(impulse,ra,-1)
		b:apply_impulse(impulse,rb,1)

		return true
	end
end

-- physic world "scene"
function make_scene()
	local physic_actors,contacts={},{}
	-- unique id per rigid body
	local _id=0x0.0001

	return {
		-- register a 3d object as a physic object
		add=function(self,a,mass,ibody_inv)
			mass=mass or 0
			local bbox=a.model
			local force,torque=v_zero(),v_zero()
			local is_static

			-- compute (inverse) inertia tensor
			if mass==0 then
				is_static=true
				ibody_inv=make_m3(0,0,0)
			end

			-- 
			local g={0,-24*mass,0}
			local rb={
				id=_id,
				static=is_static,
				-- special case for ground :/
				radius=a.extents and v_len(a.extents) or 0,
				i_inv=is_static and make_m3(0,0,0) or make_m3(),
				v=v_zero(),
				m=a.m,				
				w=v_zero(),				
				mass_inv=is_static and 0 or 1/mass,
				-- obj to world space
				pt_toworld=function(self,p)
					return transform(self.m,p)
				end,		
				-- world velocity
				pt_velocity=function(self,p)
					return v_add(self.v,v_cross(self.w,make_v(self.pos,p)))
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
					-- totally wrong but looks better!
					force=v_add(force,f,mass)
					torque=v_add(torque,v_cross(make_v(self.pos,p),f))
				end,
				-- impulse at *local* r point
				apply_impulse=function(self,f,r,sign)
					if(is_static) return
					self.v=v_add(self.v,f,sign*self.mass_inv)
					-- correct angular velocity
					self.w=v_add(
						self.w,
						rotate(
							self.i_inv,
							v_cross(r,f)
						),
						sign)
				end,
				-- apply forces & torque for iteration
				prepare=function(self,dt)
					if(is_static or self.sleeping or self.disabled) self.not_prepared=true return
					
					self.not_prepared=nil

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
				wake_up=function(self)
					self.sleeping=nil
					self.disabled=nil
					if(self.not_prepared) self:prepare(time_dt)
				end,
				integrate=function(self,dt)
					if(is_static or self.sleeping or self.disabled) return

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
			-- next body
			_id<<=1
			-- register rigid bodies
			return add(physic_actors,setmetatable(a,{__index=rb}))
		end,
		update=function()
			-- update bodies
			for _,a in pairs(physic_actors) do
				a:prepare(time_dt)
			end
			-- age contacts
			local tmp={}
			for k,c in pairs(contacts) do
				if(c.ttl>0) c.ttl-=1 tmp[k]=c
			end
			contacts=tmp

			-- collect manifolds
			local solvers={}
			for i=1,#physic_actors do
				local a=physic_actors[i]
				for j=i+1,#physic_actors do
					local b=physic_actors[j]
					local m=overlap(a,b)
					if m then
						local pid=a.id|b.id
						-- new contact?
						local ct=contacts[pid] or {ttl=0}
						if ct.ttl==0 then
							sfx(rnd{8,9,10})
							-- (re)register
							contacts[pid]=ct
						end
						-- update contact with latest info
						ct.ttl=5
						ct.manifold=m

						a.sleeping=nil
						b.sleeping=nil

						-- wake up previously touching
						--for id,ct in pairs(contacts) do
						--	if(id&a.id!=0) ct.b:wake_up()
						--	if(id&b.id!=0) ct.a:wake_up()
						--end

						-- find tangent vectors
						local tangents={make_basis(m.n)}
						for _,p in pairs(m.contacts) do										
							add(solvers,make_contact_solver(m.reference,m.incident,m.n,p,p.dist,tangents))
						end
					end
				end
			end

			-- solve manifolds
			-- multiple iterations
			-- required to fix deep contacts
			for j=1,10 do
				for i=#solvers,1,-1 do
					-- still a valid contact?
					if(not solvers[i]()) deli(solvers,i)
				end
			end
			
			-- move bodies
			for _,a in pairs(physic_actors) do
				a:integrate(time_dt)
			end
			_contacts=contacts
		end
	}
end

-->8
-- 3d engine
-- sort
-- radix sort
-- from james edge
function sort(buffer1)
  local len, buffer2, idx, count = #buffer1, {}, {}, {}

  for shift=0,5,5 do
    for i=0,31 do count[i]=0 end

    for i,b in pairs(buffer1) do
      local k=(b.key>>shift)&31
      idx[i]=k
      count[k]+=1
    end

    for i=1,31 do count[i]+=count[i-1] end

    for i=len,1,-1 do
      local k=idx[i]
      local c=count[k]
      buffer2[c]=buffer1[i]
      count[k]=c-1
    end

    buffer1, buffer2 = buffer2, buffer1
  end
end


-->8
-- tracking camera
function make_cam()
	local up={0,1,0}
	local pos={0,0,0}
	-- 
	return {
		track=function(self,o)
			-- update rotation
			local angle={0.0,0,0}
			local m=make_m_from_euler(unpack(angle))	
			-- move away from target
			local target=v_add(o.pos,m_row(m,3),8)
			target=v_add(target,{0,0,-20})
			-- max x extent
			target[1]=mid(target[1],-8,8)
			-- min height
			target[2]=5
			target[3]=min(target[3],-28)
			pos=v_lerp(pos,target,0.1)
			
			-- inverse view matrix
			self.m=make_inv_transform(m,pos)
            self.pos=pos
		end,
		project2d=function(self,p)
			p=transform(self.m,p)
			if p[3]>z_near then
				local w=128/p[3]
				return 64+p[1]*w,64-p[2]*w,w
			end
		end		
	}
end

-- callback is use to clip additional data (eg uv)
function axis_poly_clip(axis,dist,v,sign,callback)
	sign=sign or 1
	local res,v0={},v[#v]
	local d0=sign*(v0[axis]-dist)
	for i=1,#v do
		local v1=v[i]
		local d1=sign*(v1[axis]-dist)
		if d1>0 then
			if d0<=0 then
				local t=d0/(d0-d1)
				local nv=v_lerp(v0,v1,t)
				-- "fixes" clipping
				nv[axis]=dist
				res[#res+1]=nv
				if(callback) callback(i,t)
			end
			res[#res+1]=v1
			if(callback) callback(i)
		elseif d0>0 then
			local t=d0/(d0-d1)
			local nv=v_lerp(v0,v1,t)
			-- "fixes" clipping
			nv[axis]=dist
			res[#res+1]=nv
			if(callback) callback(i,t)
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
		local outcode=2
		if(az>z_near) outcode=0
		if(ax>az) outcode+=4
		if(-ax>az) outcode+=8
		if(ay>az) outcode+=16
		if(-ay>az) outcode+=32

		-- not faster :/
		-- local bo=-(((az-z_near)>>31)<<17)-(((az-ax)>>31)<<18)-(((az+ax)>>31)<<19)
		-- assert(bo==outcode,"outcode:"..outcode.." bits:"..bo)

		-- assume vertex is visible, compute 2d coords
		local a={ax,ay,az,outcode=outcode}
		t[v]=a
		return a
	end
}

function collect_faces(cam,thing,model,m,out)
	-- cam pos in object space
	local cam_pos=transform_inv(m,cam.pos)
	-- sun vector in model space
	local sun=rotate_inv(m,_sun_dir)

	-- object to world
	-- world to cam
	-- vertex cache (and model context)
	local v_cache=setmetatable({m=m_x_m(cam.m,m)},v_cache_cls)

	for _,face in pairs(model.f) do
		if v_dot(face.n,cam_pos)>face.dist then
			-- project vertices (always 4!!)
			local v0,v1,v2,v3=v_cache[face[1]],v_cache[face[2]],v_cache[face[3]],v_cache[face[4]]
			-- mix of near/far verts?
			if v0.outcode&v1.outcode&v2.outcode&v3.outcode==0 then
				local verts,uvs={v0,v1,v2,v3},face.uv
				-- mix of near+far vertices?
				if (v0.outcode|v1.outcode|v2.outcode|v3.outcode)&2!=0 then
					local uv_clipper
					if face.uv then						
						uvs={}						
						uv_clipper=function(i,t)
							-- clipped?
							local uv1=face.uv[i]
							uvs[#uvs+1]=t and v2_lerp(face.uv[i%4+1],uv1,t) or uv1
						end
					end
					verts=axis_poly_clip(3,z_near,verts,1,uv_clipper)
				end
				if #verts>2 then
					-- project + get sort key
					local key=0
					for _,v in pairs(verts) do
						local w=128/v[3]
						v.x=64+v[1]*w
						v.y=64-v[2]*w
						key+=w
					end
					verts.face=face
					verts.uvs=uvs
					verts.light=mid(-face.sign*sun[face.axis],-1,1)
					-- sort key
					verts.key=(key<<4)/#verts
					verts.thing=thing
					verts.model=model
					out[#out+1]=verts
				end
			end
		end
::skip::
	end
end

-- draw face
function draw_faces(faces,mirror)
	if mirror then
		fillp(0xf0f0.8)
	else
		fillp(0xa5a5|0b0.011)
	end
	local curbase
	for i,d in ipairs(faces) do
		if mirror then			
			polyfill(d,0x7d)			
		else
			if(d.model.shadeless) fillp()
			local base=_dithers[flr(6+6*d.light)]
			if curbase!=base then				
				curbase=base
				pal(base,2)
			end
			if d.uvs then				
				tpoly(d,d.uvs)
			else
				polyfill(d,base[d.model.color])
			end
			--if(hits and hits.reference_face==d.face) polyfill(d,11)
			--if(hits and hits.incident_face==d.face) polyfill(d,8)
			polyline(d,0)--d.thing.sleeping and 11 or 12)	
			fillp(0xa5a5|0b0.011)		
		end
	end
end

function draw_ground()
	-- texture coords
	poke4(0x5f38,0x0008.0404)

	local x0,y0=_cam:project2d({0,0,0})

	local xc,yc,zc=unpack(_cam.pos)
	local scale=4
	for y=y0\1,127 do
		local w_inv=yc/(y-64)
		local x0,z0=-64*w_inv+xc,128*w_inv+zc
		tline(0,y,127,y,x0+(w_inv*(y%1)),z0,w_inv,0)
	end

	poke4(0x5f38,0)
end

-- bold print
function bprint(s,x,y,c,c2)
	x=x or (64-#s*2)
	for i=-1,1 do
		for j=-1,1 do
			print(s,x+i,y+j,c2 or 0)
		end
	end
	print(s,x,y,c)
end

function play_state()
	local pos={0,5,-32}
	local dir,pow=0,0	
  	local ttl,score,throw,frame,scores=0,0,0,1,{}
	-- pins
	local pins,pin_positions={},{
		{0,0,0},
		{-2,0,5},
		{2,0,5},
		{-4,0,10},
		{0,0, 10},
		{4,0, 10},
	}
	local active_pins=split"1,2,3,4,5,6"
	local textures={{mx=13,c=7},{mx=15,c=4},{mx=17,c=8}}
	for i,q in pairs(pin_positions) do
		local tex=textures[i%#textures+1]
		local pin=add(pins,
					add(_things,			
						_scene:add(
							make_box(
								1,{2,6,2},
								{q[1],3,q[3]},
								make_q(v_up,0.1-rnd(0.2)),
								{mx=tex.mx,my=0,c=tex.c,[2]=true}
						),
						1.92,
						split"0.0390625, 0.0, 0.0, 0.0, 0.0, 0.19531250000000003, 0.0, 0.0, 0.0, 0.0, 0.0390625, 0.0, 0.0, 0.0, 0.0, 1"
						)
					))
		pin.location=q		
	end
	-- ball
	local ball=add(_things,			
			_scene:add(
				make_box(
					1,{2,2,2},
					v_zero(),
					make_q(v_up,0),
					{mx=0,my=rnd{8,10,12},1,2,3,4,5,6}),
					3.12,
					split"0.0732421875, 0.0, 0.0, 0.0, 0.0, 0.0732421875, 0.0, 0.0, 0.0, 0.0, 0.0732421875, 0.0, 0.0, 0.0, 0.0, 1"
				))		
	ball.friction=0.3	
	ball.disabled=true

	-- states
	local states,current_state,current_state_name,next_state
	local function next_state_handler(state)
		next_state=function()
			current_state_name=state
			current_state=states[state]()
		end
		return next_state
	end
	states={
		move=function()
			local vx=0
			ttl=20*30
			next_state_handler"direction"
			return function(self)
				-- damping      
				vx*=0.8
				if(abs(vx)<0.01) vx=0
				-- move
				local dx=0
				if(btn(0)) dx=-1
				if(btn(1)) dx=1
				if(btnp(4)) ttl=0
				vx+=dx/16
			
				pos[1]=mid(pos[1]+vx,-8,8)

				-- update public var
				self.pos=pos
			end
		end,
		direction=function()
			-- start random (to avoid button hold cheat)
			local t=rnd(30)\1
			ttl=8*30
			next_state_handler"power"
			return function()
				dir=cos(t/60)
				t+=1
				if(btnp(4)) ttl=0
			end
		end,
		power=function()
			-- start random (to avoid button hold cheat)
			local t=rnd(30)\1
			ttl=8*30
			next_state_handler"fire"
			return function()
				pow=abs(cos(t/30))
				t+=1
				if(btnp(4)) ttl=0
			end
		end,
		fire=function()
			ball.pos={pos[1],2,pos[3]}
			ball.q=make_q(v_up,0)
			if(pow>0.8) pow+=0.5 printh("power shot")
			ball.v={0,0,50+25*pow}
			ball.w={9*dir,45,9*rnd()}			
			ball:wake_up()
			--
			ttl=30
			next_state_handler"score"
			return function()
				-- wait...
				for _,p in pairs(pins) do
					if(not p.sleeping) ttl=30
				end
			end
		end,
		score=function()
			ttl=0
			-- fallen pins?
			local tmp,strike=active_pins,true
			active_pins={}
			score=0
			for i in pairs(tmp) do
				local p=pins[i]				
				if m_column(p.m,2)[2]<0.7 then
					p.disabled=true
					score+=1
				else
					active_pins[i]=true
					strike=false
				end
			end
			throw+=1
			-- all fallen?
			if strike then
				if throw==1 then
					scores[frame]="  x"
					-- end of turn
					throw=2
					next_state_handler"strike"
				else					
					scores[frame]="  /"
					next_state_handler"spare"
				end
			else
				local prev_score=scores[frame] or ""
				if(#prev_score>0) prev_score..=" "
				scores[frame]=prev_score..(score>0 and score or "-")
				next_state_handler"move"
			end
			if throw==2 then
				throw=0
				frame+=1
				active_pins=split"1,2,3,4,5,6"
			end
			-- prepare for next round
			ball.disabled=true
			for i in pairs(active_pins) do
				local p=pins[i]
				local pos=p.location
				p.pos={pos[1],3,pos[3]}
				p.q=make_q(v_up,0.1-rnd(0.2))
				p.v=v_zero()
				p.w=v_zero()
				p:wake_up()
			end			
		end,
		strike=function()
			ttl=90
			next_state_handler"move"
			return function()
				if(btnp(4)) ttl=0
			end
		end,
		spare=function()
			ttl=90
			next_state_handler"move"
			return function()
				if(btnp(4)) ttl=0
			end
		end
	}
	-- initial state
	next_state_handler("move")()
	
	return {		
		update=function(self)	
			ttl-=1
			if(ttl<0) next_state()
			-- update
			if(current_state) current_state(self)

			_cam:track(ball.disabled and {pos=pos} or ball)
		end,
		draw=function()
			-- score panel
			fillp()
			local y=19
			for i,score in ipairs(scores) do
				spr(200+(i>1 and 16 or 0),0,y-2,2,1)
				print(score,2,y,7)
				y+=8
			end			
			-- todo: revisit update/draw pattern
			if current_state_name=="move" then
				bprint("⬅️ move ➡️",nil,96,7,1)
			elseif current_state_name=="direction" then
				bprint("spin ❎",nil,96,7,1)

				rectfill(64-32*dir,104,64,109,9)
				rect(64-32*dir,104,64,109,1)
			elseif current_state_name=="power" then
				bprint("power ❎",nil,96,7,1)

				rectfill(48,104,48+32*pow,109,8)
				rect(48,104,48+32*pow,109,1)
			elseif current_state_name=="strike" then
				pal()
				map(0,14,4,24,16,4)
				local colors={8,9,10,11,4,11,10,9,8}
				for i=1,6 do
					pal(i,colors[(i+ttl\2)%#colors+1])
				end
				spr(166,24,32,10,2)
				pal()
			elseif current_state_name=="spare" then
				pal()
				map(0,18,14,24,16,4)
				local colors={8,9,10,11,4,11,10,9,8}
				for i=1,6 do
					pal(i,colors[(i+ttl\2)%#colors+1])
				end
				spr(134,38,32,7,2)
				pal()
			end

			-- display
			fillp()
			rectfill(2,2,14,16,0)
			for _,p in pairs(pins) do
				circfill(8+p.location[1],14-p.location[3],1.5,m_column(p.m,2)[2]>0.7 and 7 or 8)
			end
		end	
	}	
end

function make_box(density,extents,pos,q,uvs)
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
		color=uvs and uvs.c or 7,
		v=verts,
		-- faces
		f=faces,
		e={
			-- head/tail: vertex reference
			-- direction: axis direction
			-- normals
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
	-- base texture location
	local mx,my=uvs and uvs.mx,uvs and uvs.my

	for i,f in ipairs(faces) do
		-- direct reference to vertex
		for i=1,4 do
			f[i]=verts[f[i]]
		end
		-- index (and sign of )
		local axis=deli(f,5)
		f.axis=abs(axis)
		f.sign=sgn(axis)
		face_by_id[axis]=i
		-- find sides
		local sides={}
		for _,e in pairs(model.e) do
			if(e.normals[1]==f) add(sides,e.normals[2])
			if(e.normals[2]==f) add(sides,e.normals[1])
		end
		f.sides=sides
		-- normal
		f.n=v_zero()
		f.n[f.axis]=f.sign
		-- fast viz check
		if(uvs and uvs.flip) v_scale(f.n,-1)
		f.dist=v_dot(f.n,f[1])
		-- any texture?
		if uvs and uvs[i] then
			local scale=2*(uvs.scale or 1)
			if i==1 or i==6 then
				f.uv={
					{mx,my+scale*ez},
					{mx+scale*ex,my+scale*ez},
					{mx+scale*ex,my},
					{mx,my}
				}
				mx+=scale*ex
			end
			if i==2 or i==4 then
				f.uv={
					{mx,my+scale*ey},
					{mx+scale*ex,my+scale*ey},
					{mx+scale*ex,my},
					{mx,my}
				}
				mx+=scale*ex
			end
			if i==3 or i==5 then
				f.uv={
					{mx,my+scale*ey},
					{mx+scale*ez,my+scale*ey},
					{mx+scale*ez,my},
					{mx,my}
				}
				mx+=scale*ez
			end
		end
	end

	-- initial condition
	local m=m_from_q(q)
	m_set_pos(m,pos)

	return {
		hardness=0.2,
		friction=0.8,
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
		friction=0.8,
		model=model,
		pos=v_zero(),
		q=make_q(v_up,0),
		m=make_m3()
	}
end

-->8
-- game loop
function _init()
	_scene=make_scene()
	_state=play_state()
	_cam=make_cam()

	-- shading
	for i=0,6,0.5 do
		local dithered_fade={}    
		for j=0,15 do
			dithered_fade[j]=sget(i+0.5,j)|sget(i,j)<<4
		end
		_dithers[i*2]=dithered_fade
	end

	-- static ground
	_scene:add(make_ground())

	-- side static limits
	_scene:add(
		make_box(
			0,{20,8,64},
			{20,4,0},
			make_q(v_up,0))).friction=0
	_scene:add(
		make_box(
			0,{20,8,64},
			{-20,4,0},
			make_q(v_up,0))).friction=0
	--[[
	_scene:add(
		make_box(
			0,{20,8,2},
			{0,4,17},
			make_q(v_up,0)))
	]]
	local wall=make_box(
		0,{64,28,1},
		{0,14,0.5},
		make_q(v_up,0),
		{mx=20,my=0,scale=0.5,[2]=true})
	wall.model.shadeless=true
	local fireplace=make_box(
		0,{20,8,16},
		{0,4,8},
		make_q(v_up,0),
		{flip=true,c=5})
	_background={wall,fireplace}

	_props={
		split"80,32,24,0,20,0",
		split"104,32,16,-2,12,0",
		split"104,48,16,3,10,0"
	}

	-- tower
	--[[
	for i=1,5 do
		_a=_scene:add(make_box(
			1,{1+rnd(4),3,1+rnd(4)},
			{0,3+3*i,0},
			--make_q(v_normz({rnd(),rnd(),rnd()},rnd()))))
			make_q(v_up,rnd())))
		add(_things,_a)
	end
	_a=_scene:add(make_box(
			0,{12,3,12},
			{0,1.5,0},
			--make_q(v_normz({rnd(),rnd(),rnd()},rnd()))))
			make_q(v_up,0)))		
	add(_things,_a)
	]]

	--[[
	_a=_scene:add(make_box(
		1,{3,3,3},
		{0,0,0},
		make_q(v_normz({rnd(),rnd(),rnd()},rnd()))))
		--make_q(v_up,0)))
	_b=_scene:add(make_box(
		1,{3,3,3},
		{-2.5,0,0},
		make_q(v_normz({rnd(),rnd(),rnd()},rnd()))))
		--make_q(v_up,rnd()))
	add(_things,_a)
	add(_things,_b)
	]]
end

function _update()
	_state:update()

  	_scene:update()
	-- update fire
	srand(time())
	for mem=89*64,95*64,64 do
		memcpy(mem-64,mem,8)
	end
	for i=0,15 do
		sset(i,95,rnd{7,10})
	end
end

function _draw()
  cls(1)

	-- ground
	palt(0,true)
	fillp()
	draw_ground()
	palt(0,false)

	-- snow
	srand(40)
	for i=0,50 do
		local r=rnd()
		local v={rnd(15)+12+cos(time()*r/4),10+(rnd(20)-time())%20,rnd(20)+sin(time()*r*r/4)}
		local x0,y0,w0=_cam:project2d(v)
		pset(x0,y0,w0>2.5 and 6 or 7)
	end

	-- draw backgroud objects (unsorted)
	palt(0,true)
	local out={}
	for _,o in ipairs(_background) do
		collect_faces(_cam,o,o.model,o.m,out)
	end
	draw_faces(out)

	-- fire
	--[[
	fillp()
	palt(0,true)
	local x0,y0,w0=_cam:project2d({0,0,16})
	w0*=24/3
	local dh=w0/7
	for j=0,7 do
		palt()
		for i=0,7 do
			local c0,c1=sget(0,16+i),sget(7-j,16+i)
			pal(c0,c1)
			if(c1==0) palt(c0,true)
		end
		sspr(0,88+j,16,1,x0-w0,y0-w0+j*dh,2*w0,ceil(dh))
	end
	]]

	fillp()
	pal()
	for _,p in pairs(_props) do
		local sx,sy,sw,x,y,z=unpack(p)
		local x0,y0,w0=_cam:project2d({x,y,z})
		w0*=sw/3
		sspr(sx,sy,sw,sw,x0-w0/2,y0-w0/2,w0,w0)
	end
	
	-- draw normal
  	palt(0,false)
	local out={}
	for _,thing in pairs(_things) do
		if(not thing.disabled) collect_faces(_cam,thing,thing.model,thing.m,out)
	end

	sort(out)	
  	draw_faces(out)
	fillp()

	palt(0,true)

	_state:draw()
end

__gfx__
0000000000000000777777777777777777777777444444444444444400000000b3b3b3333333333333333333333333338888888aa88888881111111ee1111111
11111111000000007776666776666777777777774444444444444444000000003b3b333333333333333333333333333388aaa88aa88aaa8811eee11ee11eee11
11222ee700000000776000077000067777777777444444444444444400000000b3b3b3333bb3333333bb3333333bb3338aa8aa8aa8aa8aa81ee1ee1ee1ee1ee1
1533bba7000000007700000770000077777777777777777744444444000000003b3b33333333333333333333333333338a888aaaaaa888a81e111eeeeee111e1
2444499a00000000770000077000007777777777000000004444444400000000b3b3b333bbbb33333bbbb33333bbbb338aa888aaaa888aa81ee111eeee111ee1
11555677000000007700000770000077777777770000000044444444000000003b3b333333333333333333333333333388aa88aaaa88aa8811ee11eeee11ee11
1555677700000000770000077000007777777777000000004444444400000000b3b3b33bbbbbb333bbbbbb333bbbbbb3888aaaaaaaaaa888111eeeeeeeeee111
55667777000000007777777777777777777777770000000044444444000000003b3b33333bb3333333bb3333333bb333aaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee
128888e700000000777777777777777711111111444477777777444400000000b3b3b333333333333333333333333333aaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee
22499fa7000000007777777777777777111111114444777777774444000000003b3b3333333333333333333333333333888aaaaaaaaaa888111eeeeeeeeee111
299aaa7700000000777777777777777711111111444477777777444400000000b3b3b3333bb3333333bb3333333bb33388aa88aaaa88aa8811ee11eeee11ee11
5533bb77000000007777777777777777111111114444777777774444000000003b3b33333333333333333333333333338aa888aaaa888aa81ee111eeee111ee1
155dccc700000000777777a99a77777711111111444477777777444400000000b3b3b333bbbb33333bbbb33333bbbb338a888aaaaaa888a81e111eeeeee111e1
11dd66770000000077777a9999a77777111111114444777777774444000000003b3b33333333333333333333333333338aa8aa8aa8aa8aa81ee1ee1ee1ee1ee1
222eeff700000000777779999997777711111111444447777774444400000000b3b3b33bbbbbb333bbbbbb333bbbbbb388aaa88aa88aaa8811eee11ee11eee11
22eeff77000000007777749999477777111111114444444444444444000000003b3b33333bb3333333bb3333333bb3338888888aa88888881111111ee1111111
0000000000000000777777444477777744444444444444446644664400000000b3b3b3333333333333333333333333331111111ee11111118888888aa8888888
10000000000000007777777777777777422277444477222466446644000000003b3b33333333333333333333333333331111111ee11111118888888aa8888888
2110000000000000777777777777777722227744447722226644664400000000b3b3b3333333333333333333333333331111111ee11111118888888aa8888888
82210000000000007777777777777700222277444477222266666644000000003b3b33333bb3333333bb3333333bb3331111111ee11111118888888aa8888888
9882100000000000700777777777770022227044440722226666664400000000b3b3b3333333333333333333333333331111111ee11111118888888aa8888888
a9982100000000007007777777777777222270444407222244446644000000003b3b3333bbbb33333bbbb33333bbbb331111111ee11111118888888aa8888888
7aa9821000000000777700770077007742224444444422244444664400000000b3b3b3333333333333333333333333331111111ee11111118888888aa8888888
00000000000000007777007700770077444444444444444444446644000000003b3b333bbbbbb333bbbbbb333bbbbbb3eeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa
89ab3b0000000000777777777777777744444888888444444466446600000000b3b3b3333bb3333333bb3333333bb333eeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa
00000000000000007777777777777777444498888889444444664466000000003b3b33333333333333333333333333331111111ee11111118888888aa8888888
0000000000000000777777777777777744449988889944444466446600000000b3b3b3333333333333333333333333331111111ee11111118888888aa8888888
00000000000000007777777777777777444499999999444444666666000000003b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b1111111ee11111118888888aa8888888
0000000000000000677777777777777744449999999944444466666600000000b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b31111111ee11111118888888aa8888888
00000000000000006777777777777776444444444444444444664444000000003b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b1111111ee11111118888888aa8888888
0000000000000000666777777777776644444444444444444466444400000000b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b31111111ee11111118888888aa8888888
00000000000000006666777777777666444444444444444444664444000000003b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b1111111ee11111118888888aa8888888
3333333aa333333388888888888888888888888888888888ddddddddcccccccc0004400000000044000000000000000000000000000000000000000000000000
33aaa33aa33aaa3388887777777788888888888888888888ddddddddcccccccc0004400000000744000000003b3b333000000000000000007777770000000000
3aa3aa3aa3aa3aa388777777777777888888888888888888ddddddddcccccccc0004400000000744000000b333333a33b0000000000000077777777000000000
3a333aaaaaa333a3877ffffffffff7788888888888888888ddddddddcccccccc0004400000007744000033333333aaa333b00000000000077878787000000000
3aa333aaaa333aa387ff777ff777ff788888888888888888ddddddddcccccccc00044000007777440008888339111a3339330000000000006888877000000000
33aa33aaaa33aa3387ff700ff007ff788888888888888888ddddddddcccccccc0004400077777744000333881011111333330000000000000288888000000000
333aaaaaaaaaa33387ff700ff007ff788888888888888888ddddddddcccccccc000440004444444400b393120000000113888000070000000027788000000000
aaaaaaaaaaaaaaaa877ffffffffff7788888888888888888ddddddddcccccccc0004400044444444003333100000000008838000070000000067777000000000
aaaaaaaaaaaaaaaa8777ff7777ff7778222222222222222222222222111111114400000000000044033331000000000002333b00007780000088887000000000
333aaaaaaaaaa333877777000077777822222288882222228888828822222122440000000000004403a330000000000000333300077880000088888000000000
33aa33aaaa33aa33887777777777778822222882228222228888828822222122440000000000004403330000000000000003a300088887000078882000000000
3aa333aaaa333aa388887777777788882222882222772222888882882222212244000000000000440333000000000000000aaa00028777870887882000000000
3a333aaaaaa333a3888887777778888822288882227722222222222211111111440000000000004403b30000000000000003a300006788878887820000000000
3aa3aa3aa3aa3aa388888777777888882288888888882222882888882212222244000000000000440333b0000000000000333300002888878887200000000000
33aaa33aa33aaa3388888877778888882888888888888882882888882212222244000000000000440333a0000000000000339300000288788886000000000000
3333333aa33333338888887777888888888888888888888888288888221222224400000000000044003333000000000003333000000006222220000000000000
3333333aa33333338888888778888888888888866888888844444444444444440004400044700000003388800000000088833000000000000000000000000000
3333333aa333333388888887788888888888888778888888444444444444444400044000447000000008833b0000000333880000000777770000000000000000
3333333aa33333338888888778888888888888877888888844000000000000440004400044770000000833a333000b33a3380000007788877000000000000000
3333333aa333333300000a0000a0000088888887788888884400000000000044000440004477770000023aaa3333339333320000007888888000000000000000
3333333aa333333300000a0000a00000888888877888888844000000000000440004400044777777000011a33a33b33331000000008888770000000000000000
3333333aa333333388888aaaaaa88888888888877888888844000000000000440004400044777777000000113333333110000000008777770000000000000000
3333333aa33333338888888888888888888888877888888844000000000000444444444444444444000000001111111000000000007888880000000000000000
aaaaaaaaaaaaaaaa8888888888888888888888877888888844000000000000444444444444444444000000000000000000000000008888770000000000000000
aaaaaaaaaaaaaaaa8888888888888888999999990000000044000000000000444444444400000044000000004444444400000000002877777000000000044000
3333333aa33333338888888888888888444444440000000044000000000000444444444400000044000000004444444400000000006777788880000000044000
3333333aa33333338888888888888888444444440000000044000000000000440004400000000044000000000000000000000000000688888877000000044000
3333333aa33333337777777777777777444444440000000044000000000000440004400000000044000000000000000000000000000028887778800000044700
3333333aa33333337777777777777777444444440000000044000000000000440004400000000044000000000000000007777000000002877788800000744770
3333333aa33333337000000770000007444444440000000044000000000000440004400000000044000000000000000077777777000000677888200077744777
3333333aa33333330000000000000000444444440000000044444444444444440004400044444444444444440000000044444444000000022222000044444444
3333333aa33333330000000000000000444444440000000044444444444444440004400044444444444444440000000044444444000000000000000044444444
24444444444444444444444277777777444444444444444400000000000000000000000000000000000000000000000000000000000000000000000000000000
49999999999999999999999477733777422277444477222400000000000000000000000000000000000000000000000000000000000000000000000000000000
49777777777777777777779477733777222277444477222200aaa000001111102222222011111110222222201111111000aaa000000000000000000000000000
49777777777777777777779477333377222207444470222200aaa000001111102222222011111110222222201111111000aaa000000000000000000000000000
49777777777777777777779477333377222207444470222200aaa000111111102222222011111110222222201111111000aaa000000000000000000000000000
49777777777777777777779473333337222277444477222200aaa000111000002220222011101110222022201110000000aaa000000000000000000000000000
49777777777777777777779473333337422244444444222400aaa000111111102222222011111110222222201111100000aaa000000000000000000000000000
49777777777777777777779477744777444444444444444400aaa000111111102222222011111110222220001111100000aaa000000000000000000000000000
49777777777777777777779477444477444448888884444400aaa000111111102222222011111110222222201111100000aaa000000000000000000000000000
49777777777777777777779474444447444498888889444400000000000011102220000011101110222022201110000000000000000000000000000000000000
497777777777777777777794740ff047444499888899444400aaa000111111102220000011101110222022201111111000aaa000000000000000000000000000
49777777777777777777779477ffff77444499999999444400aaa000111110002220000011101110222022201111111000aaa000000000000000000000000000
49777777777777777777779477d88d77444499999999444400aaa000111110002220000011101110222022201111111000aaa000000000000000000000000000
4977777777777777777777947dddddd7444444222244444400000000000000000000000000000000000000000000000000000000000000000000000000000000
4977777777777777777777947dddddd7444444888844444400000000000000000000000000000000000000000000000000000000000000000000000000000000
4977777777777777777777947dddddd7444444888844444400000000000000000000000000000000000000000000000000000000000000000000000000000000
497777777777777777777794dddddddd000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
497777777777777777777794dddddddd000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
497777777777777777777794dddddddd0000000000000000000000aaa0000000001111102222222033333330444444405550555066666660000000aaa0000000
497777777777777777777794dddddddd0000000000000000000000aaa0000000001111102222222033333330444444405550555066666660000000aaa0000000
497777777777777777777794ddd99ddd00000000000000000000aaaaaaa000001111111022222220333333304444444055505550666666600000aaaaaaa00000
497777777777777777777794dd0dd0dd00000000000000000000aaaaaaa000001110000000222000333033300044400055505550666000000000aaaaaaa00000
499999999999999999999994d0dddd0d0000000000000000aaaaaaaaaaaaaaa0111111100022200033333330004440005555555066666000aaaaaaaaaaaaaaa0
2444444444444444444444420dddddd00000000000000000aaaaaaaaaaaaaaa0111111100022200033333000004440005555500066666000aaaaaaaaaaaaaaa0
000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaa0111111100022200033333330004440005555555066666000aaaaaaaaaaaaaaa0
00000000000000000000000000000000000000000000000000aaaaaaaaaaa00000001110002220003330333000444000555055506660000000aaaaaaaaaaa000
00000000000000000000000000000000000000000000000000aaaaaaaaaaa00011111110002220003330333044444440555055506666666000aaaaaaaaaaa000
00000000000000000000000000000000000000000000000000aaa00000aaa00011111000002220003330333044444440555055506666666000aaa00000aaa000
00000000000000000000000000000000000000000000000000aaa00000aaa00011111000002220003330333044444440555055506666666000aaa00000aaa000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
1222222222222222222210000000000000012222222222222222222100000000bbbbbbb3bbbbb700000000000000000000000000000000000000000000000000
01211221121121122211100000000000000111222112211221122210000000003333333533333370000000000000000000000000000000000000000000000000
00122222222222221111100000000000000111112222222222222100000000003333333533333337000000000000000000000000000000000000000000000000
00012222222222228888888888888888888888882222222222221000000000003333333533333333000000000000000000000000000000000000000000000000
00001222222222228228822882288228822882282222222222210000000000003333333533333333000000000000000000000000000000000000000000000000
00000122222222228888888888888888888888882222222222100000000000003333333533333333000000000000000000000000000000000000000000000000
00000012222222228888888888888888888888882222222221000000000000003333333533333333000000000000000000000000000000000000000000000000
00000001222222228888888888888888888888882222222210000000000000003333333533333333000000000000000000000000000000000000000000000000
00000000122222228888888888888888888888882222222100000000000000001111111211111100000000000000000000000000000000000000000000000000
000000000122222288888888888888888888888822222210000000000000000033333335333333b0000000000000000000000000000000000000000000000000
0000000000122222888888888888888888888888222221000000000000000000333333353333333b000000000000000000000000000000000000000000000000
00000000000122228888888888888888888888882222100000000000000000003333333533333333000000000000000000000000000000000000000000000000
00000000000012228888888888888888888888882221000000000000000000003333333533333333000000000000000000000000000000000000000000000000
00000000000001228888888888888888888888882210000000000000000000003333333533333333000000000000000000000000000000000000000000000000
00000000000000128888888888888888888888882100000000000000000000003333333533333333000000000000000000000000000000000000000000000000
00000000000000028888888888888888888888882000000000000000000000003333333533333333000000000000000000000000000000000000000000000000
00000000000000028888888888888888888888882000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000228888888888888888888888882200000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000002228888888888888888888888882220000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000022228888888888888888888888882222000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000222228888888888888888888888882222200000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000002222228888888888888888888888882222220000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000022222228888888888888888888888882222222000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000222222228888888888888888888888882222222200000000000000000000000000000000000000000000000000000000000000000000000000000000
00000002222222228888888888888888888888882222222220000000000000000000000000000000000000000000000000000000000000000000000000000000
00000022222222228888888888888888888888882222222222000000000000000000000000000000000000000000000000000000000000000000000000000000
00000222222222228888888888888888888888882222222222200000000000000000000000000000000000000000000000000000000000000000000000000000
00002222222222228228822882288228822882282222222222220000000000000000000000000000000000000000000000000000000000000000000000000000
00022222222222228888888888888888888888882222222222222000000000000000000000000000000000000000000000000000000000000000000000000000
00222222222222221111111111111111111111112222222222222200000000000000000000000000000000000000000000000000000000000000000000000000
02211221121121122211100000000000000111222112112112211220000000000000000000000000000000000000000000000000000000000000000000000000
22222222222222222222100000000000000122222222222222222222000000000000000000000000000000000000000000000000000000000000000000000000
__map__
000000000000000008090a0b0004042636545500464746474647464746474647464757575757464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000018191a1b000203242542430046474647a347a34746474647464757575757464746667b7b787b7b674647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000028292a2b0012133435525300464746808181818246474647464757575757464746767a7a687a7a774647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000038393a3b002223151664650046474690838383924647a347464757575757464746580000480000594647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000004040606626300464746a0a1a1a1a246808182464757575757464746580000480000594647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000032330505727300464746474647464746909392464757575757464746580000480000594647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000464746474647464746a0a1a2464757575757464746667b7b787b7b674647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000464746474647464746474647464757575757464746697c7c7f7c7c494647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
2e2f2e2f2e2f2e2f2e2f0c0d0000000000000000464746474647464746474647464757575757464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3e3f3e3f3e3f3e3f3e3f1c1d0000000000000000464746474647464746475656565656565656565656564647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
2c2d2c2d2c2d2c2d2c2d0e0f0000000000000000464746474647464746475600000000000000000000564647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3c3d3c3d3c3d3c3d3c3d1e1f0000000000000000464746474647464746475600000000000000000000564647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
6061606160616061606140410000000000000000464746474647464746475600000000000000000000564647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
7071707170717071707150510000000000000000747474747474747474745600000000000000000000567474747474747474747400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
c0c1c2c3c3c3c3c3c3c3c3c3c4c5c60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
d0d1d2d3d3d3d3d3d3d3d3d3d4d5d60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
e0e1e2e3d3e3d3e3d3e3d3e3d4e5e60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
f0f1f2f3f3f3f3f3f3f3f3f3f4f5f60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
c0c1c2c3c3c3c3c3c3c3c4c5c600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
d0d1d2d3d3d3d3d3d3d3d4d5d600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
e0e1e2e3d3e3d3e3d3e3d4e5e600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
f0f1f2f3f3f3f3f3f3f3f4f5f600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
__sfx__
000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00020000056500b650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000200000c65006650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000200000d6500d650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
