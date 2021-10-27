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
local _pins,_things,_scene={},{}
local _sun_dir={0,-0.707,0.707}
local _dithers={}
local _particles={}

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
function hitscan(boxes,a,b,radius)
	radius=radius or 0
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
			local plane_dist=face.dist+radius
			local dist,otherdist=face.sign*p0[face.axis],face.sign*p1[face.axis]
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

function rotate_axis(tx,axis,sign)
	axis=(axis-1)<<2
	return {sign*tx[axis+1],sign*tx[axis+2],sign*tx[axis+3]} 
end

-- http://media.steampowered.com/apps/valve/2015/DirkGregorius_Contacts.pdf
-- https://www.gdcvault.com/play/1017646/Physics-for-Game-Programmers-The
-- https://www.randygaul.net/2019/06/19/collision-detection-in-2d-or-3d-some-steps-for-success/
-- auto filled by make_box :[
local face_by_id={}

function overlap(a,b)
	if(a.static and b.static) return
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
	--out.n=rotate_axis(out.reference.m,reference_face.axis,reference_face.sign)
	--local n=rotate(out.reference.m,reference_face.n)
	--local nr=n[1].." "..n[2].." "..n[3]
	--local no=out.n[1].." "..out.n[2].." "..out.n[3]
	--assert(nr==no,nr.." vs "..no)
	-- find incident face		
	local incident_face=out.incident:incident_face(out.n)
	out.incident_face=incident_face
	-- clip incident with reference sides
	-- convert incident face into reference space
	for i=1,4 do
		add(contacts,transform(tx,incident_face[i]))
	end
	for _,side in pairs(reference_face.sides) do
		-- for some reason clipping removed all points
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
	-- cannot touch ground
	if(b.pos[2]>b.radius) return

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
		-- to world space
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
					if(is_static or self.sleeping) self.not_prepared=true return
					
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
					if(self.not_prepared) self:prepare(time_dt)
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
			target[3]=min(target[3],-20)
			target[1]=mid(target[1],-8,8)
			pos=v_lerp(pos,target,0.1)
			
			-- inverse view matrix
			self.m=make_inv_transform(m,pos)
            self.pos=pos

			local m=make_m_from_euler(-angle[1],angle[2],angle[3])	
            --
			local x,y,z=unpack(pos)
            self.m_mirror=m_x_m(m3_transpose(m),{
				1,0,0,0,
				0,1,0,0,
				0,0,1,0,
				-x,y,-z,1
			})
            self.pos_mirror={x,-y,z}
		end,
		project2d=function(self,p)
			p=transform(self.m,p)
			if p[3]>z_near then
				local w=128/p[3]
				printh(p[3].." w:"..w)
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
		ay*=(t.flip and -1 or 1)
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
	local v_cache=setmetatable({m=m_x_m(cam.m,m),flip=cam.flip or false},v_cache_cls)

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

	local xc,yc,zc=unpack(_cam.pos)
	local scale=4
	for y=64,127 do
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

function make_player(pos)
	local dir,pow=0,0	
  	local ttl=0
	-- states
	local states,current_state,next_state
	local draw_mode="move"

	states={
		move=function()
			local vx=0
			ttl=20*30
			next_state=states.direction
			printh("move")
			return function(self)
				-- damping      
				vx*=0.8
				if(abs(vx)<0.01) vx=0
				-- move
				local dx=0
				if(btn(0,1)) dx=-1
				if(btn(1,1)) dx=1
				if(btnp(4)) ttl=0
				vx+=dx/16

				pos[1]+=vx
				-- update public var
				self.pos=pos
			end
		end,
		direction=function()
			printh("dir")
			draw_mode="dir"
			-- start random (to avoid button hold cheat)
			local t=rnd(30)\1
			ttl=8*30
			next_state=states.power
			return function()
				dir=cos(t/60)
				t+=1
				if(btnp(4)) ttl=0
			end
		end,
		power=function()
			printh("power")
			draw_mode="power"
			-- start random (to avoid button hold cheat)
			local t=rnd(30)\1
			ttl=8*30
			next_state=states.fire
			return function()
				pow=abs(cos(t/30))
				t+=1
				if(btnp(4)) ttl=0
			end
		end,
		fire=function()
			printh("fire")
			draw_mode=nil
			_ball=add(_things,			
				_scene:add(
					make_box(
						1,{2,2,2},
						{pos[1],2,pos[3]},
						make_q(v_up,0),
						{mx=0,my=rnd{8,10,12},1,2,3,4,5,6}),
						3.12,
						{0.0732421875, 0.0, 0.0, 0.0, 0.0, 0.0732421875, 0.0, 0.0, 0.0, 0.0, 0.0732421875, 0.0, 0.0, 0.0, 0.0, 1}
					))		
			_ball.friction=0.3	
			_ball.v={0,0,50+25*pow}
			_ball.w={9*dir,45,9*rnd()}
			
			--
			ttl=0			
			return states.score()
		end,
		score=function()
			next_state=states.move
			printh("score")
			return function()
				ttl=5
			end
		end
	}
	current_state=states.move()
	-- 
	return {		
		update=function(self)	
			ttl-=1
			if(ttl<0) current_state=next_state()
			-- update
			if(current_state) current_state(self)
		end,
		draw=function()
			if draw_mode=="move" then
				bprint("⬅️ move ➡️",nil,96,7,1)
			elseif draw_mode=="dir" then
				bprint("spin ❎",nil,96,7,1)

				rectfill(64-32*dir,104,64,109,9)
				rect(64-32*dir,104,64,109,1)
			elseif draw_mode=="power" then
				bprint("power ❎",nil,96,7,1)

				rectfill(48,104,48+32*pow,109,8)
				rect(48,104,48+32*pow,109,1)
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
	-- capture mouse
	-- enable lock+button alias
	-- poke(0x5f2d,7)

	_scene=make_scene()
	_plyr=make_player({0,5,-32})
	_cam=make_cam()

	palt(0,false)
	-- shading
	for i=0,6,0.5 do
		local dithered_fade={}    
		for j=0,15 do
			dithered_fade[j]=sget(i+0.5,j)|sget(i,j)<<4
		end
		_dithers[i*2]=dithered_fade
	end

	_scene:add(make_ground())

	local pins={
		{0,0,0},
		{-2,0,5},
		{2,0,5},
		{-4,0,10},
		{0,0, 10},
		{4,0, 10},
	}
	local textures={{mx=13,c=7},{mx=15,c=4},{mx=17,c=8}}
	for i,q in pairs(pins) do
		local tex=textures[i%#textures+1]
		add(_pins,
			add(_things,			
				_scene:add(
					make_box(
						1,{2,6,2},
						{q[1],3,q[3]},
						--make_q(v_normz({rnd(),rnd(),rnd()},rnd()))
						make_q(v_up,0.1-rnd(0.2)),
						{mx=tex.mx,my=0,c=tex.c,[2]=true}
				),
				1.92,
				{0.0390625, 0.0, 0.0, 0.0, 0.0, 0.19531250000000003, 0.0, 0.0, 0.0, 0.0, 0.0390625, 0.0, 0.0, 0.0, 0.0, 1}
				)
			)).location=q
	end

	_scene:add(
		add(_things,
			make_box(
				0,{20,8,10},
				{18,4,5},
				make_q(v_up,0),
				{c=5})
	)).friction=1
	_scene:add(
		add(_things,
			make_box(
				0,{20,8,10},
				{-18,4,5},
				make_q(v_up,0),
				{c=5})
	)).friction=1
	add(_things,
		make_box(
			0,{16,8,10},
			{0,12,5},
			make_q(v_up,0),
			{c=5}))

	_wall=make_box(
		0,{48,28,1},
		{0,14,0.5},
		make_q(v_up,0),
		{mx=24,my=0,scale=0.5,[2]=true})
	_wall.model.shadeless=true
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
	_plyr:update()
	_cam:track(_ball or _plyr)

	for i=#_particles,1,-1 do
		local p=_particles[i]
		p.ttl-=1
		if p.ttl<0 then
			deli(_particles,i)
		else
			local next_pos=v_add(p.pos,p.v,4)
			local hit=hitscan(_things,next_pos,p.pos)
			if hit then
				local f=v_normz(make_v(p.pos,next_pos))					
				v_scale(f,175)
				hit.owner:add_force(f,hit)
				deli(_particles,i)
			elseif next_pos[2]<0.25 then
				deli(_particles,i)
			else
				p.pos=next_pos
				p.v[2]-=0.05
			end
		end
	end

    _scene:update()

end

function _draw()
    cls(1)

	-- mirror image
	--[[
    local out,mirror_cam={},{pos=_cam.pos_mirror,m=_cam.m_mirror,flip=true}
	for _,thing in pairs(_things) do
		collect_faces(mirror_cam,thing,thing.model,thing.m,out)
	end

    draw_faces(out,true)
	]]
	
	-- ground
	palt(0,true)
	fillp()
	draw_ground()
	palt(0,false)

	-- draw normal
    local out={}
	for _,thing in pairs(_things) do
		collect_faces(_cam,thing,thing.model,thing.m,out)
	end

	sort(out)

	--[[
	_b.pos={-5*cos(time()/16),2.5,0}
	m_set_pos(_b.m,_b.pos)	
	local hits=overlap(_a,_b)
	]]
    draw_faces(out)
	fillp()
	
	palt(0,true)
	out={}
	collect_faces(_cam,_wall,_wall.model,_wall.m,out)
	draw_faces(out)

	for _,p in pairs(_particles) do
		local x0,y0,w0=_cam:project2d(p.pos)
		if w0 then
			circfill(x0,y0,w0,6)
			circ(x0,y0,w0,7)
		end
	end

	palt(0,true)
	--local x0,y0,w0=_cam:project2d({0,0,0})
	--smap(20,0,32,13,x0,y0,w0/4)


	_plyr:draw()

	-- display pins map
	fillp()
	for _,p in pairs(_pins) do
		circfill(8+p.location[1],12-p.location[3],1.5,m_column(p.m,2)[2]>0.7 and 7 or 8)
	end
end

__gfx__
000000008888888a777777777777777777777777444444444444444444444444b3b3b3333333333333333333333333338888888aa88888881111111ee1111111
111111118888888a7776666776666777777777774444444444444444774444773b3b333333333333333333333333333388aaa88aa88aaa8811eee11ee11eee11
11222ee78888888a776000077000067777777777444444444444444477444477b3b3b3333bb3333333bb3333333bb3338aa8aa8aa8aa8aa81ee1ee1ee1ee1ee1
1533bba78888888a7700000770000077777777777777777744444444774444773b3b33333333333333333333333333338a888aaaaaa888a81e111eeeeee111e1
2444499a8888888a770000077000007777777777000000004444444470444407b3b3b333bbbb33333bbbb33333bbbb338aa888aaaa888aa81ee111eeee111ee1
115556778888888a7700000770000077777777770000000044444444704444073b3b333333333333333333333333333388aa88aaaa88aa8811ee11eeee11ee11
155567778888888a770000077000007777777777000000004444444444444444b3b3b33bbbbbb333bbbbbb333bbbbbb3888aaaaaaaaaa888111eeeeeeeeee111
55667777aaaaaaaa7777777777777777777777770000000044444444444444443b3b33333bb3333333bb3333333bb333aaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee
128888e7aaaaaaaa777777777777777711111111444477777777444448888884b3b3b333333333333333333333333333aaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee
22499fa78888888a7777777777777777111111114444777777774444988888893b3b3333333333333333333333333333888aaaaaaaaaa888111eeeeeeeeee111
299aaa778888888a777777777777777711111111444477777777444499888899b3b3b3333bb3333333bb3333333bb33388aa88aaaa88aa8811ee11eeee11ee11
5533bb778888888a7777777777777777111111114444777777774444999999993b3b33333333333333333333333333338aa888aaaa888aa81ee111eeee111ee1
155dccc78888888a777777a99a77777711111111444477777777444499999999b3b3b333bbbb33333bbbb33333bbbb338a888aaaaaa888a81e111eeeeee111e1
11dd66778888888a77777a9999a77777111111114444777777774444444444443b3b33333333333333333333333333338aa8aa8aa8aa8aa81ee1ee1ee1ee1ee1
222eeff78888888a777779999997777711111111444447777774444444444444b3b3b33bbbbbb333bbbbbb333bbbbbb388aaa88aa88aaa8811eee11ee11eee11
22eeff778888888a7777749999477777111111114444444444444444444444443b3b33333bb3333333bb3333333bb3338888888aa88888881111111ee1111111
00000000a8888888777777444477777744444444777777776644664494494494b3b3b3333333333333333333333333331111111ee11111114444444444444444
00000000a88888887777777777777777444444447777777766446644494949443b3b33333333333333333333333333331111111ee11111114222774444772224
00000000a8888888777777777777777744044044777777776644664444999444b3b3b3333333333333333333333333331111111ee11111112222774444772222
00000000a88888887777777777777700444004447777777766666644444944443b3b33333bb3333333bb3333333bb3331111111ee11111112222774444772222
00000000a8888888700777777777770044400444777777776666664494494494b3b3b3333333333333333333333333331111111ee11111112222704444072222
00000000a88888887007777777777777440440447777777744446644494949443b3b3333bbbb33333bbbb33333bbbb331111111ee11111112222704444072222
00000000a8888888777700770077007744444444477777744444664444999444b3b3b3333333333333333333333333331111111ee11111114222444444442224
00000000aaaaaaaa7777007700770077444444444444444444446644444944443b3b333bbbbbb333bbbbbb333bbbbbb3eeeeeeeeeeeeeeee4444444444444444
00000000aaaaaaaa777777777777777700000000444444444466446644444444b3b3b3333bb3333333bb3333333bb333eeeeeeeeeeeeeeee4444488888844444
00000000a88888887777777777777777000000004444222244664466222244443b3b33333333333333333333333333331111111ee11111114444988888894444
00000000a8888888777777777777777700000000444222224466446622222444b3b3b3333333333333333333333333331111111ee11111114444998888994444
00000000a88888887777777777777777000000004442222244666666222224443b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b1111111ee11111114444999999994444
00000000a8888888677777777777777700000000444222224466666622222444b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b31111111ee11111114444999999994444
00000000a88888886777777777777776000000004442222244664444222224443b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b1111111ee11111114444444444444444
00000000a8888888666777777777776600000000444422224466444422224444b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b31111111ee11111114444444444444444
00000000a88888886666777777777666000000004444444444664444444444443b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b1111111ee11111114444444444444444
3333333aa333333388888888888888888888888888888888ddddddddcccccccc0000000000000000000000000000000000000000000000000000000000000000
33aaa33aa33aaa3388887777777788888888888888888888ddddddddcccccccc0000000000000000000000000000000000000000000000000000000000000000
3aa3aa3aa3aa3aa388777777777777888888888888888888ddddddddcccccccc0000000000000000000000000000000000000000000000000000000000000000
3a333aaaaaa333a3877ffffffffff7788888888888888888ddddddddcccccccc0000000000000000000000000000000000000000000000000000000000000000
3aa333aaaa333aa387ff777ff777ff788888888888888888ddddddddcccccccc0000000000000000000000000000000000000000000000000000000000000000
33aa33aaaa33aa3387ff700ff007ff788888888888888888ddddddddcccccccc0000000000000000000000000000000000000000000000000000000000000000
333aaaaaaaaaa33387ff700ff007ff788888888888888888ddddddddcccccccc0000000000000000000000000000000000000000000000000000000000000000
aaaaaaaaaaaaaaaa877ffffffffff7788888888888888888ddddddddcccccccc0000000000000000000000000000000000000000000000000000000000000000
aaaaaaaaaaaaaaaa8777ff7777ff7778222222222222222222222222111111119999999900000000000000000000000000000000000000000000000000000000
333aaaaaaaaaa3338777770000777778222222888822222288888288222221224444444400000000000000000000000000000000000000000000000000000000
33aa33aaaa33aa338877777777777788222228822282222288888288222221224444444400000000000000000000000000000000000000000000000000000000
3aa333aaaa333aa38888777777778888222288222277222288888288222221224444444400000000000000000000000000000000000000000000000000000000
3a333aaaaaa333a38888877777788888222888822277222222222222111111114444444400000000000000000000000000000000000000000000000000000000
3aa3aa3aa3aa3aa38888877777788888228888888888222288288888221222224444444400000000000000000000000000000000000000000000000000000000
33aaa33aa33aaa338888887777888888288888888888888288288888221222224444444400000000000000000000000000000000000000000000000000000000
3333333aa33333338888887777888888888888888888888888288888221222224444444400000000000000000000000000000000000000000000000000000000
3333333aa33333338888888778888888888888866888888800000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa33333338888888778888888888888877888888800000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa33333338888888778888888888888877888888800000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa333333300000a0000a00000888888877888888800000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa333333300000a0000a00000888888877888888800000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa333333388888aaaaaa88888888888877888888800000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa33333338888888888888888888888877888888800000000000000000000000000000000000000000000000000000000000000000000000000000000
aaaaaaaaaaaaaaaa8888888888888888888888877888888800000000000000000000000000000000000000000000000000000000000000000000000000000000
aaaaaaaaaaaaaaaa8888888888888888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa33333338888888888888888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa33333338888888888888888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa33333337777777777777777000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa33333337777777777777777000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa33333337000000770000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa33333330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3333333aa33333330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
__map__
260636060606000008090a0b0004042636545500464746474647464746474647464746575747464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
350737060606000018191a1b0002032e2f424300464746474647464746474647464746575747464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
061706062506000028292a2b0012133e3f525300464746474647464746474647464746575747464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
062506060606000038393a3b0022231516646500464746474647464746474647464757575757464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0606060606060000000000000004040606626300464746474647464746474647464757575757464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0514050514050000000000000032330505727300464746474647464746474647464757575757464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000464746474647464746474647464757575757464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000464746474647464746474647464757575757464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
012101210121012101210c0d0000000000000000464746474647464746474647464757575757464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
113111311131113111311c1d0000000000000000464746474647464746474656565656565656565656474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
2c2d2c2d2c2d2c2d2c2d0e0f0000000000000000464746474647464746474656202020202020202056474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3c3d3c3d3c3d3c3d3c3d1e1f0000000000000000464746474647464746474656202020202020202056474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
6061606160616061606140410000000000000000464746474647464746474656202020202020202056474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
7071707170717071707150510000000000000000464746474647464746474656202020202020202056474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000585858585858585858585856202020202020202056585858585858585858585800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
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
