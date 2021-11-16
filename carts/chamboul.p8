pico-8 cartridge // http://www.pico-8.com
version 33
__lua__
-- totally accurate holiday bowling
-- by @freds72
-- physic code based on Randy Gaul articles & sources:
-- https://github.com/RandyGaul/qu3e

#include polyfill.lua
#include math.lua

-- globals
local _sun_dir={0,-0.707,0.707}
local _dithers={}

-- camera
local _cam
local k_far,k_near=0,2
local k_right,k_left=4,8
local k_up,k_down=16,32
local z_near=1

-- physic thresholds+baumgarte
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
	local bias=-k_bias*min(dist+k_slop)*30

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

	-- sound register
	-- 1: ground
	-- 2: title box
	-- 4: throwing ball
	-- 8: pin
	local sounds={
		-- ground/box (game)
		[0b0101]={8,9,10},
		-- pin/pin
		[0b1000]={12,13,14},
		-- pin/box
		[0b1100]={15},
		-- ground/pin
		[0b1001]={16,17,18}
	}
	return {
		-- register a 3d object as a physic object
		add=function(self,a,mass,ibody_inv)
			mass=mass or 0
			local bbox=a.model
			local force,torque,is_static=v_zero(),v_zero()

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
				prepare=function(self)
					if(is_static or self.sleeping or self.disabled) self.not_prepared=true return
					
					self.not_prepared=nil

					-- add gravity
					force=v_add(force,g)
				
					-- inverse inertia tensor
					self.i_inv=m3_x_m3(m3_x_m3(self.m,ibody_inv),m3_transpose(self.m))
			
					-- velocity
					self.v=v_add(self.v,force,self.mass_inv/30)
			
					-- angular velocity
					self.w=v_add(self.w,rotate(self.i_inv,torque),1/30)
					
					-- friction
					v_scale(self.v,1/(1+0.4/30))
					v_scale(self.w,1/(1+0.6/30))
				end,
				wake_up=function(self)
					self.sleeping=nil
					self.disabled=nil
					if(self.not_prepared) self:prepare()
				end,
				integrate=function(self)
					if(is_static or self.sleeping or self.disabled) return

					-- clear forces
					force,torque=v_zero(),v_zero()

					-- no significant velocity/angular v?
					if(v_dot(self.v,self.v)<k_small and v_dot(self.w,self.w)<k_small_v) self.sleeping=true self.v=v_zero() self.w=v_zero() return

					self.pos=v_add(self.pos,self.v,1/30)
					q_dydt(self.q,self.w,1/30)
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
				a:prepare()
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
							local sfxid=bor(a.material,b.material)
							if(sounds[sfxid]) sfx(rnd(sounds[sfxid]))
							-- (re)register
							contacts[pid]=ct
						end
						-- update contact with latest info
						ct.ttl=3
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
				a:integrate()
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
			-- basis
			local m=make_m3()
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
		end
	end
end
function draw_ground()
	palt(0,true)
	fillp()
	local x0,y0=_cam:project2d({0,0,0})

	local xc,yc,zc=unpack(_cam.pos)
	local scale=4
	for y=y0\1,127 do
		local w_inv,scale=yc/(y-64),1
		local x0,z0=-64*w_inv+xc,128*w_inv+zc
		-- switch mipmap?
		if w_inv>1/8 then
			poke4(0x5f38,0x0e34.0810)
			scale=0.5
		else
			poke4(0x5f38,0x0e14.1020)
		end
		tline(0,y,127,y,(16+x0)*scale+(w_inv*(y%1)),z0*scale,w_inv*scale,0)
	end

	poke4(0x5f38,0)
	palt(0,true)
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

-- attach given key/value pair string to the given table
function with_properties(t,props)
	local kv=split(props)
	for i=1,#kv,2 do
		t[kv[i]]=kv[i+1]
	end
	return t
end

function title_state()
	local ttl,seed=30,rnd()
	local scene,things=make_scene(),{}
	-- static ground
	scene:add(make_ground())
	scene:add(make_box(
		0,{64,32,2},
		{0,16,1},
		make_q(v_up,0)))

	music(0)
	return
		-- update
		function()		
			ttl-=1
			if(ttl<0 and #things!=4) then
				ttl=30+rnd(4)
				srand(time()+seed)
				local i=#things
				-- no material = no sound
				add(things,			
					scene:add(
						with_properties(
							make_box(
								1,{8-i,2,8-i},
								{4-rnd(8),20,-20+rnd()},
								make_q(v_up,0.1-rnd(0.2)),
								{mx=52,my=2*i,[2]=true,scale=4/(8-i),c=4}),
						"friction,0.4"),
					1.92/(1+i/2),
					split"0.0390625, 0.0, 0.0, 0.0, 0.0, 0.0390625, 0.0, 0.0, 0.0, 0.0, 0.0390625, 0.0, 0.0, 0.0, 0.0, 1"
					)
				)
			end
			scene:update()

			_cam:track({pos={0,5,-28}})

			if(btn()!=0) music(-1,250) next_state(play_state)
		end,
		function()
			palt(0,false)
			local out={}
			for _,thing in pairs(things) do
				collect_faces(_cam,thing,thing.model,thing.m,out)
			end

			sort(out)	
			draw_faces(out)
			palt(0,true)

			fillp()
			if(ttl%16<8) bprint("press any button",nil,108,8,7)
			bprint("@freds72",nil,120,1,7)
		end
end

function play_state()
	local pos={0,5,-32}
	local dir,pow=0,0	
  	local ttl,score,throw,frame,scores=0,0,0,1,{}
	-- physic scene	
	local scene=make_scene()
	scene:add(make_ground())

	-- side static limits
	for _,pos in pairs{split"20,4,0",split"-20,4,0"} do
		scene:add(
			with_properties(
				make_box(
					0,
					{20,8,64},
					pos,
					make_q(v_up,0)),
					"friction,0"
				))
	end
	-- pins
	local things,pins,pin_positions={},{},{
		split"0,0,0",
		split"-2,0,5",
		split"2,0,5",
		split"-4,0,10",
		split"0,0, 10",
		split"4,0, 10",
	}
	local active_pins=split"1,2,3,4,5,6"
	local textures={{mx=13,c=7},{mx=15,c=4},{mx=17,c=8}}
	for i,q in pairs(pin_positions) do
		local tex=textures[i%#textures+1]
		local pin=add(pins,
					add(things,			
						scene:add(
							with_properties(
								make_box(
									1,
									split"2,6,2",
									{q[1],3,q[3]},
									make_q(v_up,0.1-rnd(0.2)),
									{mx=tex.mx,my=0,c=tex.c,[2]=true}),
								"material,8"
						),
						1.92,
						split"0.0390625, 0.0, 0.0, 0.0, 0.0, 0.19531250000000003, 0.0, 0.0, 0.0, 0.0, 0.0390625, 0.0, 0.0, 0.0, 0.0, 1"
						)
					))
		pin.location=q		
	end
	-- ball
	local ball=add(things,			
			scene:add(
				with_properties(
					make_box(
						1,
						split"2,2,2",
						v_zero(),
						make_q(v_up,0),
						{mx=0,my=rnd{8,10,12},1,2,3,4,5,6}),
					"friction,0.3,disabled,true,material,4"),
				3.12,
				split"0.0732421875, 0.0, 0.0, 0.0, 0.0, 0.0732421875, 0.0, 0.0, 0.0, 0.0, 0.0732421875, 0.0, 0.0, 0.0, 0.0, 1"))

	-- fx effect
	local banner_y
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
			end
		end,
		direction=function()
			-- start random (to avoid button hold cheat)
			local t=rnd(30)\1
			ttl=8*30
			sfx(51)
			next_state_handler"power"
			return function()
				dir=cos(t/60)
				t+=1
				if(btnp(4)) ttl=0 sfx(51,-2)
			end
		end,
		power=function()
			-- start random (to avoid button hold cheat)
			local t=rnd(30)\1
			ttl=8*30
			sfx(50)
			next_state_handler"fire"
			return function()
				pow=abs(cos(t/30))
				t+=1
				if(btnp(4)) ttl=0 sfx(50,-2)
			end
		end,
		fire=function()
			ball.pos={pos[1],2,pos[3]}
			ball.q=make_q(v_up,0)
			if(pow>0.8) pow+=0.25
			ball.v={0,0,50+25*pow}
			ball.w={9*dir,45,9*rnd()}			
			ball:wake_up()
			--
			ttl=30
			sfx(10)
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
					banner_y=-20
					next_state_handler"strike"
				else					
					scores[frame]="  /"
					banner_y=-20
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
			sfx(11)
			next_state_handler"move"
			return function()
				if(btnp(4)) ttl=0
			end
		end,
		spare=function()
			ttl=90
			sfx(11)
			next_state_handler"move"
			return function()
				if(btnp(4)) ttl=0
			end
		end
	}
	-- initial state
	next_state_handler("move")()
	
	return
		-- update
		function()	
			scene:update()

			ttl-=1
			if(ttl<0) next_state()
			-- update
			if(current_state) current_state()

			_cam:track(ball.disabled and {pos=pos} or ball)
		end,
		-- draw
		function()
			-- pins
			palt(0,false)
			local out={}
			for _,thing in pairs(things) do
				if(not thing.disabled) collect_faces(_cam,thing,thing.model,thing.m,out)
			end

			sort(out)	
			draw_faces(out)
			palt(0,true)

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
				banner_y=lerp(banner_y,24,0.2)
				pal()
				map(0,14,4,banner_y,16,4)
				local colors={8,9,10,11,4,11,10,9,8}
				for i=1,6 do
					pal(i,colors[(i+ttl\2)%#colors+1])
				end
				spr(166,24,banner_y\1+8,10,2)
				pal()
			elseif current_state_name=="spare" then
				banner_y=lerp(banner_y,24,0.2)
				pal()
				map(0,18,14,banner_y,16,4)
				local colors={8,9,10,11,4,11,10,9,8}
				for i=1,6 do
					pal(i,colors[(i+ttl\2)%#colors+1])
				end
				spr(134,38,banner_y\1+8,7,2)
				pal()
			end

			-- display
			fillp()
			rectfill(2,2,14,16,0)
			for _,p in pairs(pins) do
				circfill(8+p.location[1],14-p.location[3],1.5,m_column(p.m,2)[2]>0.7 and 7 or 8)
			end
		end
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
	
	return with_properties({
			model=model,
			pos=v_zero(),
			q=make_q(v_up,0),
			m=make_m3()
		},
		"material,1,is_ground,true,mass,0,hardness,0.2,friction,0.8")
end

-->8
-- game loop + state mgt
function next_state(fn,...)
  local u,d,i=fn(...)
  -- ensure update/draw pair is consistent
  _update_state=function()
    -- init function (if any)
    if(i) i()
    -- 
    _update_state,_draw_state=u,d
    -- actually run the update
    u()
  end
end

function _init()
	-- glocal cam
	_cam=make_cam()
	-- startup state
	next_state(title_state)
	-- back to menu
	menuitem(1,"back to menu",function()
		next_state(title_state)
	end)

	-- fillp shading
	for i=0,6,0.5 do
		local dithered_fade={}    
		for j=0,15 do
			dithered_fade[j]=sget(i+0.5,j)|sget(i,j)<<4
		end
		_dithers[i*2]=dithered_fade
	end

	-- fire shading
	for j=0,7 do
		pal()
		for i=0,7 do
			local c0,c1=sget(0,16+i),sget(7-j,16+i)
			pal(c0,c1)
			palt(c0,c1==0)
		end
		memcpy(0x4300+16*j,0x5f00,16)
		
	end

	-- background props
	local wall=make_box(
		0,
		split"64,28,1",
		split"0,14,0.5",
		make_q(v_up,0),
		{mx=20,my=0,scale=0.5,[2]=true})
	wall.model.shadeless=true
	local fireplace=make_box(
		0,
		split"20,8,16",
		split"0,4,8",
		make_q(v_up,0),
		{flip=true,c=5})
	_background={wall,fireplace}

	_props={
		split"80,32,24,0,20,0",
		split"104,32,16,-2,12,0",
		split"104,48,16,3,10,0"
	}
end

function _update()
	_update_state()

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
	draw_ground()

	-- snow
	srand(40)
	for i=0,50 do
		local r=rnd()
		local v={rnd(15)+12+cos(time()*r/4),10+(rnd(20)-time())%20,rnd(20)+sin(time()*r*r/4)}
		local x0,y0,w0=_cam:project2d(v)
		pset(x0,y0,w0>2.5 and 6 or 7)
	end

	-- draw backgroud objects (unsorted)
	local out={}
	for _,o in ipairs(_background) do
		collect_faces(_cam,o,o.model,o.m,out)
	end
	draw_faces(out)
	fillp()

	-- fire (custom palette )
	local x0,y0,w0=_cam:project2d({0,0,24})
	w0*=24/3
	local dh=w0/7
	local cdh=ceil(dh)
	for j=0,7 do
		memcpy(0x5f00,0x4300+16*j,16)
		sspr(0,88+j,16,1,x0-w0+1,y0-w0+j*dh,2*w0,cdh)
	end

	pal()
	for _,p in pairs(_props) do
		local sx,sy,sw,x,y,z=unpack(p)
		local x0,y0,w0=_cam:project2d({x,y,z})
		w0*=sw/3
		sspr(sx,sy,sw,sw,x0-w0/2,y0-w0/2,w0,w0)
	end
	
	_draw_state()
end

__gfx__
00000000bbbbbbbb77777777777777777777777744444444444444449999994433b3b3b3b3b3b3b3b3b3b333333333338888888aa88888881111111ee1111111
11111111bbbbbbbb7776666776666777777777774444444444444444999999443b3b3b3b3b3b3b3b3b3b3b333333333388aaa88aa88aaa8811eee11ee11eee11
11222ee7bbbbbbbb776000077000067777777777444444444444444499999944b3bbbbbbbbbbbbbbbbbbb3b3333333338aa8aa8aa8aa8aa81ee1ee1ee1ee1ee1
1533bba7bbbbbbbb7700000770000077777777777777777744444444999999443bbbbbbbbbbbbbbbbbbbbb3b333333338a888aaaaaa888a81e111eeeeee111e1
2444499abbbbbbbb770000077000007777777777000000004444444499999944b3bbbbbbbbbbbbbbbbbbbbb3333333338aa888aaaa888aa81ee111eeee111ee1
11555677bbbbbbbb7700000770000077777777770000000044444444999999443bbbb33333333333333bbb3b3333333388aa88aaaa88aa8811ee11eeee11ee11
15556777bbbbbbbb770000077000007777777777000000004444444499999944b3bbb33333333333333bbbb333333333888aaaaaaaaaa888111eeeeeeeeee111
55667777bbbbbbbb7777777777777777777777770000000044444444999999443bbbb33333333333333bbb3b33333333aaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee
128888e733333333777777777777777711111111444477777777444444444444b3bbb33333333333333bbbb333333333aaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee
22499fa7333663337777777777777777111111114444777777774444444444443bbbb333333bb333333bbb3bb333333b888aaaaaaaaaa888111eeeeeeeeee111
299aaa7733888833777777777777777711111111444477777777444499999944b3bbb33333333333333bbbb33333333388aa88aaaa88aa8811ee11eeee11ee11
5533bb77388877837777777777777777111111114444777777774444999999443bbbb33333bbbb33333bbb3bbb3333bb8aa888aaaa888aa81ee111eeee111ee1
155dccc738888783777777a99a77777711111111444477777777444499999944b3bbb33333333333333bbbb3333333338a888aaaaaa888a81e111eeeeee111e1
11dd66773828888377777a9999a77777111111114444777777774444999999443bbbb3333bbbbbb3333bbb3bbbb33bbb8aa8aa8aa8aa8aa81ee1ee1ee1ee1ee1
222eeff738228883777779999997777711111111444447777774444499999944b3bbb333333bb333333bbbb3b333333b88aaa88aa88aaa8811eee11ee11eee11
22eeff77338888337777749999477777111111114444444444444444999999443bbbb33333333333333bbb3b333333338888888aa88888881111111ee1111111
00000000dddddddd777777444477777744444444444444446644664499949994b3bbb33333333333333bbbb3333333331111111ee11111118888888aa8888888
10000000d77dd77d7777777777777777422277444477222466446644999499943bbbb33333333333333bbb3b333333331111111ee11111118888888aa8888888
21100000d88dd88d777777777777777722227744447722226644664499949994b3bbb33333333333333bbbb3333333331111111ee11111118888888aa8888888
82210000d77dd77d7777777777777700222277444477222266666644444499943bbbbbbbbbbbbbbbbbbbbb3bbbbbbbbb1111111ee11111118888888aa8888888
98821000d88dd88d700777777777770022227044440722226666664499949994b3bbbbbbbbbbbbbbbbbbbbb3bbbbbbbb1111111ee11111118888888aa8888888
a9982100d77dd77d7007777777777777222270444407222244446644999499943b3bbbbbbbbbbbbbbbbbbb3b333333331111111ee11111118888888aa8888888
7aa98210d77dd77d77770077007700774222444444442224444466449994999433b3b3b3b3b3b3b3b3b3b3b3333333331111111ee11111118888888aa8888888
00000000dddddddd777700770077007744444444444444444444664499949994333b3b3b3b3b3b3b3b3b3b3333333333eeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa
89ab3b007777777777777777777777774444488888844444446644669994999488888888888888888888888888888888eeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa
0000000077777777777777777777777744449888888944444466446699949994888888888888888888888888888888881111111ee11111118888888aa8888888
0000000088888888777777777777777744449988889944444466446699949994777887787778777878887888787888881111111ee11111118888888aa8888888
0000000088888888777777777777777744449999999944444466666699944444878878788788787878887888787888881111111ee11111118888888aa8888888
0000000088888888677777777777777744449999999944444466666699949994878878788788777878887888777888881111111ee11111118888888aa8888888
0000000077777777677777777777777644444444444444444466444499949994878878788788787878887888887888881111111ee11111118888888aa8888888
0000000077777777666777777777776644444444444444444466444499949994878877888788787877787778777888881111111ee11111118888888aa8888888
0000000077777777666677777777766644444444444444444466444499949994888888888888888888888888888888881111111ee11111118888888aa8888888
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
24444444444444444444444277777777444444444444444400000000000000000000000000000000000000000000000000000000333333333333333333333333
49999999999999999999999477733777422277444477222400000000000000000000000000000000000000000000000000000000333333333333333333333333
49777777777777777777779477733777222277444477222200aaa000001111102222222011111110222222201111111000aaa000838338838333888388338883
49777777777777777777779477333377222207444470222200aaa000001111102222222011111110222222201111111000aaa000838383838333383383838383
49777777777777777777779477333377222207444470222200aaa000111111102222222011111110222222201111111000aaa000888383838333383383838883
49777777777777777777779473333337222277444477222200aaa000111000002220222011101110222022201110000000aaa000838383838333383383838383
49777777777777777777779473333337422244444444222400aaa000111111102222222011111110222222201111100000aaa000838388338883888388838383
49777777777777777777779477744777444444444444444400aaa000111111102222222011111110222220001111100000aaa000333333333333333333333333
49777777777777777777779477444477444448888884444400aaa000111111102222222011111110222222201111100000aaa000333333332a33338200000000
49777777777777777777779474444447444498888889444400000000000011102220000011101110222022201110000000000000333333333288a8a300000000
497777777777777777777794740ff047444499888899444400aaa000111111102220000011101110222022201111111000aaa00083833553332a223300000000
49777777777777777777779477ffff77444499999999444400aaa000111110002220000011101110222022201111111000aaa000838338733333333300000000
49777777777777777777779477d88d77444499999999444400aaa000111110002220000011101110222022201111111000aaa000888388873333333300000000
4977777777777777777777947dddddd7444444222244444400000000000000000000000000000000000000000000000000000000338328883333333300000000
4977777777777777777777947dddddd7444444888844444400000000000000000000000000000000000000000000000000000000888332833333333300000000
4977777777777777777777947dddddd7444444888844444400000000000000000000000000000000000000000000000000000000333333333333333300000000
497777777777777777777794ddddddddcccccccccccccccc00000000000000000000000000000000000000000000000000000000000000000000000000000000
497777777777777777777794ddddddddcccccccccccccccc00000000000000000000000000000000000000000000000000000000000000000000000000000000
497777777777777777777794dddddddd000cc00c0c0c0ccc000000aaa0000000001111102222222033333330444444405550555066666660000000aaa0000000
497777777777777777777794dddddddd0c0c0c0c0c0c0ccc000000aaa0000000001111102222222033333330444444405550555066666660000000aaa0000000
497777777777777777777794ddd99ddd00cc0c0c0c0c0ccc0000aaaaaaa000001111111022222220333333304444444055505550666666600000aaaaaaa00000
497777777777777777777794dd0dd0dd0c0c0c0c000c0ccc0000aaaaaaa000001110000000222000333033300044400055505550666000000000aaaaaaa00000
499999999999999999999994d0dddd0d000c00cc000c000caaaaaaaaaaaaaaa0111111100022200033333330004440005555555066666000aaaaaaaaaaaaaaa0
2444444444444444444444420dddddd0ccccccccccccccccaaaaaaaaaaaaaaa0111111100022200033333000004440005555500066666000aaaaaaaaaaaaaaa0
00000000000000000000000000000000ccccccccccccccccaaaaaaaaaaaaaaa0111111100022200033333330004440005555555066666000aaaaaaaaaaaaaaa0
00000000000000000000000000000000cccccccccccccccc00aaaaaaaaaaa00000001110002220003330333000444000555055506660000000aaaaaaaaaaa000
00000000000000000000000000000000000c00ccc00ccccc00aaaaaaaaaaa00011111110002220003330333044444440555055506666666000aaaaaaaaaaa000
00000000000000000000000000000000c0cc0c0c0ccccccc00aaa00000aaa00011111000002220003330333044444440555055506666666000aaa00000aaa000
00000000000000000000000000000000c0cc0c0c0ccccccc00aaa00000aaa00011111000002220003330333044444440555055506666666000aaa00000aaa000
00000000000000000000000000000000c0cc0c0c0c0ccccc00000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000c0c0c000ccccc00000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000cccccccccccccccc00000000000000000000000000000000000000000000000000000000000000000000000000000000
1222222222222222222210000000000000012222222222222222222100000000bbbbbbb3bbbbb70033333333333333333bbbbbbbbbbbbbbbbbbbbbb300000000
012112211211211222111000000000000001112221122112211222100000000033333335333333703333333bb3333333bbbbbbbbbbbbbbbbbbbbbbbb00000000
00122222222222221111100000000000000111112222222222222100000000003333333533333337333333bbbb333333bb33333333333333333333bb00000000
000122222222222288888888888888888888888822222222222210000000000033333335333333333333333333333333bb33333333333333333333bb00000000
000012222222222282288228822882288228822822222222222100000000000033333335333333333333333333333333bb33333333333333333333bb00000000
000001222222222288888888888888888888888822222222221000000000000033333335333333333333bbbbbbbb3333bb3333b333b333b333b333bb00000000
00000012222222228888888888888888888888882222222221000000000000003333333533333333333bbbbbbbbbb333bb333bbb3bbb3bbb3bbb33bb00000000
000000012222222288888888888888888888888822222222100000000000000033333335333333333333333333333333bb33333333333333333333bb00000000
000000001222222288888888888888888888888822222221000000000000000011111112111111003333333333333333bb33333333333333333333bb00000000
000000000122222288888888888888888888888822222210000000000000000033333335333333b033b3b3b3b3b3b333bb33333b33b333b3b33333bb00000000
0000000000122222888888888888888888888888222221000000000000000000333333353333333b3b3b3b3b3b3b3b33bb3333333bbb3bbb333333bb00000000
000000000001222288888888888888888888888822221000000000000000000033333335333333333333333333333333bb3333bb33333333bb3333bb00000000
000000000000122288888888888888888888888822210000000000000000000033333335333333333333333333333333bb33333333333333333333bb00000000
000000000000012288888888888888888888888822100000000000000000000033333335333333333333333bb3333333bb333bbb33b333b3bbb333bb00000000
00000000000000128888888888888888888888882100000000000000000000003333333533333333333333bbbb333333bb33333b3bbb3bbbb33333bb00000000
000000000000000288888888888888888888888820000000000000000000000033333335333333333333333333333333bb33333333333333333333bb00000000
000000000000000288888888888888888888888820000000000000000000000000000000000000000000000000000000bb33333333333333333333bb00000000
000000000000002288888888888888888888888822000000000000000000000000000000000000000000000000000000bb33333333b333b3333333bb00000000
000000000000022288888888888888888888888822200000000000000000000000000000000000000000000000000000bb3333333bbb3bbb333333bb00000000
000000000000222288888888888888888888888822220000000000000000000000000000000000000000000000000000bb33333333333333333333bb00000000
000000000002222288888888888888888888888822222000000000000000000000000000000000000000000000000000bb33333333333333333333bb00000000
000000000022222288888888888888888888888822222200000000000000000000000000000000000000000000000000bb33333333333333333333bb00000000
000000000222222288888888888888888888888822222220000000000000000000000000000000000000000000000000bb333333bbbbbbbb333333bb00000000
000000002222222288888888888888888888888822222222000000000000000000000000000000000000000000000000bb333333bbbbbbbb333333bb00000000
0000000222222222888888888888888888888888222222222000000000000000bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb00000000000000000000000000000000
0000002222222222888888888888888888888888222222222200000000000000bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb00000000000000000000000000000000
0000022222222222888888888888888888888888222222222220000000000000777bb77bb77b7b7b777b777b777b777b00000000000000000000000000000000
00002222222222228228822882288228822882282222222222220000000000007b7b7bbb7bbb7b7b7b7b7b7bb7bb7bbb00000000000000000000000000000000
0002222222222222888888888888888888888888222222222222200000000000777b7bbb7bbb7b7b77bb777bb7bb77bb00000000000000000000000000000000
00222222222222221111111111111111111111112222222222222200000000007b7b7bbb7bbb7b7b7b7b7b7bb7bb7bbb00000000000000000000000000000000
02211221121121122211100000000000000111222112112112211220000000007b7bb77bb77bb77b7b7b7b7bb7bb777b00000000000000000000000000000000
2222222222222222222210000000000000012222222222222222222200000000bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb00000000000000000000000000000000
__label__
cdd99ddccccccdddddddccccccdddddddccccccddddddccccccc1111111111111111111111111dddddddccccccddddddd4111111111111111111114411111111
cd1ddddccccccdddddddccccccdddddddccccccddddddccccccc2122222212222212222222222dddddddccccccddddddd4111111111111111111114411111111
c1ddd1dccccccdddddddccccccdddddddccccccddddddccccccc2122222212222212222222222dddddddccccccddddddd4111116111111111111114411111111
cddddd1ccccccdddddddccccccdddddddccccccddddddccccccc2122222212222212222222222dddddddccccccddddddd4116111111111111116114411111111
9999999999999dddddddccccccdddddddccccccddddddccccccc22221223b3bb3332222222212dddddddccccccddddddd4111111111111111611114411111111
7777777777779dddddddccccccdddddddccccccddddddccccccc22221b3333333a33b22222212dddddddccccccddddddd4117111111111111111114411111111
7777777777779dddddddccccccdddddddccccccddddddccccccc222333333333aaa333b222212dddddddccccccddddddd4111111161111111611114411111111
7777777777779dddddddccccccdddddddccccccddddddccccccc1188883391111a33393311111dddddddccccccddddddd4111111171111111111114411161111
7777777777779dddddddccccccdddddddccccccddddddccccccc2133388111111113333322222dddddddccccccddddddd4444444444444444444444444444444
7777777777779dddddddccccccdddddddccccccddddddccccccc2b39312212222211138882222dddddddccccccddddddd4444444444444444444444444444444
7777777777779dddddddccccccdddddddccccccddddddccccccc1333311111111111188381111dddddddccccccddddddd4111716111111111111114411111111
7773377777779dddddddccccccdddddddccccccddddddccccccc333312222212222222333b212dddddddccccccddddddd4111111111111117161114411111111
7733377777779dddddddccccccdddddddccccccddddddccccccc3a33122222122222223333212dddddddccccccddddddd4111111111111111111114411111111
7733377777779dddddddccccccddd9dddccccccddddddccccccc33311111111111111113a3111dddddddccccccddddddd4111111111111111111114411111111
7333337777779dddddddccccccdd1d1ddccccccddddddccccccc3332222212222212222aaa222dddddddccccccddddddd4111611111111111111114411111111
7333337777779dddddddccccccd1ddd1dccccccddddddccccccc3332222212222212222aaa222dddddddccccccddddddd4111111111111111117114411111111
7777777777779ddddddd2444444444444444442ddddddccccccc3b311111111111111113a3111dddddddccccccddddddd4111111111111111111114411111111
7777777777779ddddddd4999999999999999994ddddddccccccc333b122222122222223333212dddddddccccccddddddd4111111111111111111114411111111
7777777777779ddddddd4777777777777777794ddddddccccccc333a122222122222223393212dddddddccccccddddddd4111111111111111111114411116111
7777777777779ddddddd4777777777777777794ddddddccccccc2333322222122222233332212dddddddccccccddddddd4111111111116111111164411111111
7777777777779ddddddd4777777777777777794ddddddccccccc2338882212222212888332222dddddddccccccddddddd4111111111111111111114411111111
9999999999999ddddddd4777777777777777794ddddddccccccc218833b212222213338822222dddddddccccccddddddd4111111111111111111114411161111
4444444444444ddddddd4777777777777777794ddddddccccccc21833a3332222b33a33822222dddddddccccccddddddd4111111111111111111114416111111
cddddddccccccddddddd4777777744477777794ddddddccccccc1123aaa333333393333211111dddddddccccccddddddd4111111161111111111114411111111
cddddddccccccddddddd477777741f147777794ddddddccccccc22211a33a333b333312222212dddddddccccccddddddd4111111111111111171114411111111
cddddddccccccddddddd47777777fff77777794ddddddccccccc2222111333333331122222212dddddddccccccddddddd4111111111111111111114411111111
cddddddccccccddddddd47777777d8d77777794ddddddccccccc1111111111111111111111111dddddddccccccddddddd4111111111111111111114411111111
cddddddccccccddddddd4777777ddddd7777794ddddddccccccc2122222212222212222222222dddddddccccccddddddd4111111111111111111114411111111
cddddddccccccddddddd4777777ddddd7777794ddddddccccccc2122222212222212222222222dddddddccccccddddddd4111111111111111111114411111111
cddddddccccccddddddd4777777777777777794ddddddccccccc1111111111111111111111111dddddddccccccddddddd4444444444444444444444444444444
cddddddccccccddddddd4777777777777777794ddddddccccccc2222122222122222222222212dddddddccccccddddddd4444444444444444444444444444444
cddddddccccccddddddd4777777777777777794ddddddccccccc2222122222122222222222212dddddddccccccddddddd4117111111111111111114411111111
cddddddccccccddddddd4777777777777777794ddddddccccccc1111111111111111111111111dddddddccccccddddddd4111111111111711111114411171111
cddddddccccccddddddd4777777777777777794ddddddccccccc2122222212222212222222222dddddddccccccddddddd4111111111111111111114411111111
cddddddccccccddddddd4999999999999999994ddddddccccccc2122227777772212222222222dddddddccccccddddddd4111111111111111111114411111111
cddddddccccccddddddd2444444444444444442ddddddccccccc2122777777777212222222222dddddddccccccddddddd4111111111111111111114411111111
cddddddccccccdddddddccccccdddddddccccccddddddccccccc2222777878787222222222212dddddddccccccddddddd4711111111111111711114411111111
cddddddccccccdddddddccccccdddddddccccccddddddccccccc2222126888877222222222212dddddddccccccddddddd4771111111111111111114411111111
cddddddccccccdddddddccccccdddddddccccccddddddccccccc2222122288888222222222212dddddddccccccddddddd4777111111111111111114471111111
cddddddccccccdddddddccccccdddddddccccccddddddccccc7c1111111127788111111111111dddddddccccccddddddd4777771777111777111674471177711
cddddddccccccdddddddccccccdddddddccccccddddddccccc7c2122222267777212777777222dddddddccccccddddddd4444444444444444444444444444444
cddddddccccccdddddddccccccdddddddccccccddddddccccc7c2122222267777217788877722dddddddccccccddddddd4444444444444444444444444444444
cddddddccccccdddddddccccccdddddddccccccddddddcccccc77811111188887117888888811dddddddccccccdddddddccccccddddddcccccccddddddcccccc
cddddddccccccdddddddccccccdddddddccccccddddddccccc778822122288888228888777212dddddddccccccdddddddccccccddddddcccccccddddddcccccc
cddddddccccccdddddddccccccdddddddccccccddddddccccc888872122278882228777777212dddddddccccccdddddddccccccddddddcccccccddddddcccccc
cddddddccccccdddddddccccccdddddddccccccddddddccccc287778771887882117888888111dddddddccccccdddddddccccccddddddcccccccddddddcccccc
cddddddccccccdddddddccccccdddddddccccccddddddcccccc67888778887822218888777222dddddddccccccdddddddccccccddddddcccccccddddddcccccc
cddddddccccccdddddddccccccdddddddccccccddddddcccccc28888778887222218888777222dddddddccccccdddddddccccccddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc22222222222222222222222222288788888622222287777772222222222222222222222222222ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc88882888888888888288888288886222222828888677778888888882888888288888288888888ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc88882888888888888288888288888828888828888868888888778882888888288888288888888ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc88882888888888800088888288888828888828888882888877788882888888288888288888888ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc882888882880000f0c08828888828888882888882888287777888288888288888828888828888ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc88288888000ffff0ccc0828888828888882888882888867778882288888288888828888828888ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc88288800ffffff0ccccc000000000000000000000000002222220000000000000000000828888ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc2222220ffffff0ccccccc07777777777777777777777777777777777777777777700050222222ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc888820ffffff0cccccccc07777777777777777777700077777777777777777700055550888888ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc88880ffffff0cc0ccccccc0000000000000000000000000000000000000000055555550888888ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc2220ffffff0cc00ccccccc601111111111000fff00bbb01111111111111110555555550222222ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc880ffffff0ccccccccccc6660111111100ffff00bbb6b01111111111111110555555550828888ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc80ffffff0cccc00c00cc667760111100ffff00bbbb667b0111111111111110555555550828888ddddddcccccccddddddcccccc
cddddddccccccdddddddcccccc0ffffff0cc0ccc0000c66678760100ffff00bbbbbbb8770111111111111110555555550222222ddddddcccccccddddddcccccc
cddddddccccccdddddddccccc0ffffff0cc00c0cc00c6666677000ffff00bbbbb88bb8888011111111111110555555550888888ddddddcccccccddddddcccccc
cddddddccccccdddddddccc00ffffff0cccc0cc0ccc667766600ffff00bbbbb8bb8b8e88b011111111111110555555550888888ddddddcccccccddddddcccccc
cddddddccccccdddddddcc0ffffff00cc00cc0cc0cc6678760ffff00bbbb88bb8888bee8bb01111111111110555555550222222ddddddcccccccddddddcccccc
cddddddccccccdddddddc0ffffff0ccc00cccc0ccc6666770fff00bbbbb8bb8b8bb8bbbbbe01111111111110555555550828888ddddddcccccccddddddcccccc
cddddddccccccddddddd0ffffff0cccc0c0ccc0cc6766660ff00bbbb8bb8888bbb88bbbb8ab0111111111110555555550828888ddddddcccccccddddddcccccc
cddddddccccccdddddd0ffffff0cccccccc000cc6778660f00bbbbb8b88b8b88b8bbbbba8ab0111111111110555555550828888ddddddcccccccddddddcccccc
cddddddccccccddddd0ffffff0ccccccccc00cc666877000bbbb88b8bb8b88b8bbbab88ae001111111111110555555550888888ddddddcccccccddddddcccccc
cddddddccccccdddd0ffffff0ccc00ccccc0cc67666700bbbb888bbb8b88b8bbbeeae8a00111111111111110555555550888888ddddddcccccccddddddcccccc
cddddddccccccddd0ffffff0ccc0c00cccccc6778660bbbbbbbb8bbb8b88bbb00ebbb0011111111111111110555555550888888ddddddcccccccddddddcccccc
cddddddccccccdd0ffffff0cccc00c00c0cc6668770bbb8bbbbbb8bbb88bbbb0400000111111111111111110555555550222222ddddddcccccccddddddcccccc
cddddddccccccd0ffffff0ccc00c00cc0cc6666670bb8bb8bbbbb888bbbabba0444400000001111111111110555555550828888ddddddcccccccddddddcccccc
cddddddcccccc0ffffff0ccccc00c00ccc6776660bb888b8bbbb888bbeea88044444444000f0000111111110555555550828888ddddddcccccccddddddcccccc
9999999999990ffffff0ccc00cc0000cc66788760bb8b8bb8b88bbbb8ebeee044444444444000ff0000011105555555502222229999999999999999999999999
44444444444440ffff0cccc0c0cc00cc6666878088b8b88b888bbbbbabbb00044444444444444000ffff00000555555508888884444444444444444444444444
4444444444444400f0ccccc0cc0cccc67766680bb8b88b8bbbbbbbb8ab00110444444444444444440000fffff000055508888884444444444444444444444444
44444444444444400ccc00c00ccccc6678866008888b88bbbbaab8ae00111104444444444444444440bb0000fffff00002222224444444444444444444444444
444444444444444400c000ccc00cc66668780040bb8b88bbeeee8e001111104444444444444444440bbbbbbb00000ffff0008884444444444444444444444444
4444444444444444440000c0cccc6676668000008b88bbbb8bbeb0111111104444444444444444440bbbbbbbbbbbb0000fff0000444444444444444444444444
0000000000000000000000c00cc66788660fffff0bbbbbb8abb000000000004444444444444444440777bbbbbbbbbbbbb00000ff000000000000000000000000
994999499499999949940000cc66668770ffffff0bbbb8a8e00fffffffffff0044444444444444440777bbb77bbbbbbbbbbbbb0000f000949994994994999499
994999499999949994900000c66666670ffffffff0ae88e00fffffffffffffff04444444444444407bb7bbb77bbb7bbbbbbbbbbbbb0000000949994994999499
9994999999499949900fff0066786660fffffffff0bee00ffffffffffffffffff0044444444444407777b7bbbbbb77bb7bbbbbbbbbbbbb000000049994994999
99949994999499000ffffff00688760fffffffffff000ffffffffffffffffffffff0444444444440777bb7bbbb7bbbb77b7bb7bbbbbbbbbbbbb0000049994999
49999499949900fffffffffff06770ffffffffffff0fffffffffffffffffffffffff0444444444407b7bb7bbbb7bbbb77b7bb7777b7bbbbbbbbbbbb000499944
99499949990000000000000000000000000000000ffffffffffffffffffffffffffff00444444407bb7b77bbbb7bbbb7bb7b77b7bb7777b7bbbbbbbbb0999499
99994999490888888888888888888888888888888000000000000000000000000000000044444407b77bbbbbb77bbbb7b77b7bb7b77b7bb7777b77bbb0949999
9499994999088888888888888888888888888888888888888888888888888888888888030044440bbb7bb777bb7bbb77b7bb77bbb77b7bbb7bbb777704999949
9994999949088888888888888888888888888888888888888888888888888888888888033b04440bbbbbbbb7bb777bb7b7bb7b77b7777bbb7bbb7bbb09944999
949999499908888888888888888888888888888888888888888888888888888888888803333000bbbbbbbbbbbbbb7bb777b77b7bb7b77bb77bb777bb04999949
99994999940777778888777788777778877777788778888877888888778778888888880333bbb000bbbbbbbbbbbbbbbbb7b7bb7b77b7bbb7bbb777bb09949999
9444444499077777888877778877777887777778877888887788888878877888888888033bbbbbb3000000bbbbbbbbbbbbbbbbbb7bb7bbb7bbb7bbb049999444
49999499990887888877887788887888877887788778888877888888788778888888880333333333333333000000bbbbbbbbbbbbbbbbbbb7bbb777b094499994
999499999408878888778877888878888778877887788888778888887887788888888803bbbbbbbbb333bbbbbbbb000000bbbbbbbbbbbbbbbbb777b099944999
94999994490887888877887788887888877777788778888877888888777778888888880333333333333333333333333333000000bbbbbbbbbbbbbbb099999449
9999944999088788887788778888788887777778878888887788888877777888888888033333333333333333333333333333bbb9000000bbbbbbbb0994999994
9994499999088788887788778888788887788778878888887788888888877888888888033bbbbbbbbbb333bbbbbbbbbb33333bbb999994000000bb0999449999
994444444408878888777788888878888778877887777788778888888887788888888803333bbbbbbb333333bbbbbbb3333333bbb99999444444000999994444
49999994990887888877778888887888877887788777778877777788777778888888880333333bbb33333333333bbb333333333bbbb999994499999449999944
99999449990888888888888888888888888888888888888888888888888888888888880333333333333333333333333333333333bbbb99999449999944999999
99944999990000000000000000000000000000000888888888888888888888888888880333bbbbbbbbbbb3333bbbbbbbbbbb33333bbbb9999944999999449999
9944444444499999944bbbb3333333bbbbbbbb33300000000000000000000000000000033333bbbbbbbb3333333bbbbbbbb3333333bbbb444444449999944444
449999994499999944bbbb333333333bbbb333333333333bbbb333333333333bbb333333333333bbbb333333333333bbbb333333333bbbb99999944999999449
99999944999999443bbbb333333333333333333333333333333333333333333333333333333333333333333333333333333333333333bbb3b999999449999994
999994499999944b3bbb33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333bbbb399999944999999
999944999999443bbbb333333b3b3b3b3b3b33333b3bb3b3b3b3b33333b3b3b3bb3b3b33333b3b3b3b3b33b33333b3b3b3b3b3b3333333bbb3b9999994499999
99449999999443bbbb333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333bbb3b999999944999
944999999444b3bbb33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333bbbb399999994499
499999994433bbbb33333333333bbb333333333333333bbb333333333333333bbb333333333333333bbb333333333333333bbb33333333333bbb3bb444444444
9999999443bbbbb333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333bbb33b99999994
99999944b3bbbb33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333bbbbb39999999
9999444b3bbbb33333b3b3bb3b3b33b3b3333b3b33b3b3bb3b3b3333b3bb3b3b33b3b33b333bb3b3b33b3b3bb3b3333b3b3bb3b3b33b3b333333bbbbb3999999
999444b3bbbb333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333bbbbb399999
9944bb3bbbb3333333bbbbbbbbbbbbb3333333bbbbbbbbbbbbb3333333bbbbbbbbbbbbb3333333bbbbbbbbbbbbb3333333bbbbbbbbbbbbb3333333bbbbb33999
944bb3bbbb3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333bbbbb3399
44b33bbbb33333333333bbbbb3333333333333333bbbbb3333333333333333bbbbb3333333333333333bbbbb3333333333333333bbbbb33333333333bbbbbb39
4b33bbbb33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333bbbbbb3
b3bbbb3333333333333bbbbb3333333333333333bbbbbb3333333333333333bbbbb3333333333333333bbbbbb3333333333333333bbbbb3333333333333bbbbb
bbbbb33333333333333bbb3333333333333333333bbb33337777777777777777777377777777777733333bbb3333333333333333333bbb33333333333333bbbb
bbbb3333333333333333333333333333333333333333333771771117111711171177711711171117333333333333333333333333333333333333333333333bbb
bbb3333333bb3bb3b33b33b33b3333333bb3b33b33b33b371717177717171777171717777717771733b3bb3bb3bb3b33333333b3bb3bb3bb3b33b333333333bb
bb33333333333333333333333333333333333333333333371717117711771177171711173717111733333333333333333333333333333333333333333333333b
b333333333bbbbbbbbbbbbbbb333333333bbbbbbbbbbbbb7177717771717177717177717371717773bbbbbbbbbbbbbb333333333bbbbbbbbbbbbbbb333333333
3333333333bbbbbbbbbbbb333333333333bbbbbbbbbbbb3771171737171711171117117737171117333bbbbbbbbbbbb333333333333bbbbbbbbbbbb333333333
33333333333333333333333333333333333333333333333377777737777777777777777337777777333333333333333333333333333333333333333333333333
333333333333bbbbbb3333333333333333333bbbbbb333333333333333333bbbbbbb333333333333333333bbbbbb3333333333333333333bbbbbb33333333333
3333333333333bbb3333333333333333333333bbb3333333333333333333333bbb3333333333333333333333bbb3333333333333333333333bbb333333333333

__map__
38393a3b00000000000000040404042636545500464746474647464746474647464757575757464746474647464746474647464738393a3b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
b0b1b2b30000000000000031310203242542430046474647a347a34746474647464757575757464746667b7b787b7b674647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
8d8e8f9d9e000000000000313112133435525300464746808181818246474647464757575757464746767a7a687a7a7746474647f8f9fafb010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
a4a5b4b50000000000000004042223151664650046474690838383924647a347464757575757464746580000480000594647464701010101010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000040404040606626300464746a0a1a1a1a24680818246475757575746474658000048000059464746478d8e8f9d0b0b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000000000000000000000032333233050572730046474647464746474690939246475757575746474658000048000059464746479e9e9e9e0b0b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000464746474647464746a0a1a2464757575757464746667b7b787b7b6746474647a4a5b4b5474700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000464746474647464746474647464757575757464746697c7c7f7c7c494647464721212121464600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
2e2f2e2f2e2f2e2f2e2f0c0d0000000000000000464746474647464746474647464757575757464746474647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3e3f3e3f3e3f3e3f3e3f1c1d0000000000000000464746474647464746475656565656565656565656564647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
2c2d2c2d2c2d2c2d2c2d0e0f0000000000000000464746474647464746475600000000000000000000564647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3c3d3c3d3c3d3c3d3c3d1e1f0000000000000000464746474647464746475600000000000000000000564647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
6061606160616061606140410000000000000000464746474647464746475600000000000000000000564647464746474647464700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
7071707170717071707150510000000000000000747474747474747474745600000000000000000000567474747474747474747400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
c0c1c2c3c3c3c3c3c3c3c3c3c4c5c600000000000717071707170717071718cacbcacbcacbcacbcacb1a071707170717071707172727272727dc1b1b1b1bde2727272727000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
d0d1d2d3d3d3d3d3d3d3d3d3d4d5d600000000000707070707070707070718dadbdadbdadbdadbdadb1a070707070707070707073737373737dc1b1b1b1bde3737373737000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
e0e1e2e3d3e3d3e3d3e3d3e3d4e5e600000000001707170717071707170718cacbcacbcacbcacbcacb1a170717071707170717072727272727dc1b1b1b1bde2727272727000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
f0f1f2f3f3f3f3f3f3f3f3f3f4f5f600000000000707070707070707070718dadbdadbdadbdadbdadb1a070707070707070707073737373737dc1b1b1b1bde3737373737000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
c0c1c2c3c3c3c3c3c3c3c4c5c6000000000000000717071707170717071718cacbcacbcacbcacbcacb1a071707170717071707172727272727dc1b1b1b1bde2727272727000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
d0d1d2d3d3d3d3d3d3d3d4d5d6000000000000000707070707070707070718dadbdadbdadbdadbdadb1a070707070707070707073737373737dc1b1b1b1bde3737373737000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
e0e1e2e3d3e3d3e3d3e3d4e5e6000000000000001707170717071707170718cacbcacbcacbcacbcacb1a170717071707170717072727272727dc1b1b1b1bde2727272727000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
f0f1f2f3f3f3f3f3f3f3f4f5f6000000000000000707070707070707070718dadbdadbdadbdadbdadb1a070707070707070707073737373737dc1b1b1b1bde3737373737000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000717071707170717071718cacbcacbcacbcacbcacb1a071707170717071707172727272727dc1b1b1b1bde2727272727000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000707070707070707070718dadbdadbdadbdadbdadb1a0707070707070707070700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000001707170717071707170718cacbcacbcacbcacbcacb1a1707170717071707170700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000707070707070707070718dadbdadbdadbdadbdadb1a0707070707070707070700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000717071707170717071718cacbcacbcacbcacbcacb1a0717071707170717071700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000707070707070707070718dadbdadbdadbdadbdadb1a0707070707070707070700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000001707170717071707170718cacbcacbcacbcacbcacb1a1707170717071707170700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000707070707070707070718dadbdadbdadbdadbdadb1a0707070707070707070700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
__sfx__
010a00002a5342a5322a5322a5352a5342a5352753427532275322753227532275323062500000000000000003130031353062500000000000000006130061352a5342a5322a5322a5352a5342a5352353423532
010a00000000000000000000000000000000003061500000000000000030615000000313003130031300313030625000000613006130061300613030625000000813008130081300813030625000003061500000
010a00002753427532275322753527534275352a5342a5322a5322a5322a5322a5353061500000000000000000000000003062500000000000000000000000002753427532275322753527534275352753427532
010a00000000000000000000000000000000003062500000000000000000000000002753227532275322753227532275322753227532275322753227532275353062500000000000000008130081353062500000
010a000023532235352753427532306250000000000000000313003135306250000000000000000613006135275342753227532275352a5342a53530625000000000000000001200012530625000000000000000
010a00000000000000306150000003130031300313003130306250000006130061300613006130306250000008130081300813008130306250000000120001200012000120306150000000130001300013000130
010a000027532275352a5342a5353061500000000000000000000000003062500000000000000000000000002a5342a5322a5322a535275342753530615000000000000000000000000030615000000000000000
010a0000000000000000000000002753227532275322753227532275322753227532275322753227532275353062500000000000000008130081352a5342a5322a5322a5322a5322a5322a5322a5322a5322a532
000300000c1600e151101411213113121141111511115115000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000300000b1600b1510b1410b1310b1210d1111111112115000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000300000b1601015114141171311a1211c1111d1011e1051f1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000400002f3402f3402f3403434034340343403433034330343303433034330343203432034310343103431034310343103431500300003000030000300003000030000300003000030000300003000030000300
000600001135305330103030430310303107031070513005306041070310705000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000300001235008341003010130500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000600000e3500432114101171011a1011c1011d1011e1051f1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00060000141500f3000c3300b32000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000500001b65010630000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00030000126500d640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000200002f650156400f640066500060000600013000f000130001800007500055000250000500005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000300001a6501c6300d6500361003610000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
010a00000013000135306250000000000000000113001135306250000000000000002a5342a535306250000000000000002a5342a532306250000000000000000013000135306250000000000000002a5342a535
010a00003062500000011300113001130011303062500000031300313003130031303062500000255342553500000000003061500000001300013000130001303062500000011300113001130011303062500000
010a00000000000000306250000000000000000000000000306250000000000000002553425535306150000000000000002553425535306150000000000000000000000000306250000000000000002753427535
010a00002a5322a5322a5322a535000000000000000000002a5342a535000000000003130031352853428535000000000000000000002a5322a5322a5322a5350000000000000000000000000000000113001135
010a00002c5342c535000000000029534295352e5342e5322e5322e5352e5342e5352e5342e5322e5322e53528534285323062500000000000000001130011353062500000000000000003130031352a5342a532
010a00000313003130031300313030625000003061500000000000000030615000003061500000000000000030625000000113001130011300113030625000000313003130031300313030625000003061500000
010a0000285342853500000000002d5342d5352a5342a5322a5322a5352a5342a5352a5342a5322a5322a5352c5342c5353062500000000000000000000000003062500000000000000000000000002753427532
010a00003062500000000000000003130031353062500000000000000000000000003062500000000000000000000000002853228532285322853228532285322853228532285322853228532285353062500000
010a00002a5322a5352a5342a53527534275350000000000285342853230625000000000000000011300113530625000000000000000031300313527534275350000000000235342353523534235350000000000
010a00000000000000306150000030615000000000000000306250000001130011300113001130306250000003130031300313003130306250000030615000000000000000306150000030615000000000000000
010a0000275322753527534275352a5342a5350000000000255342553530625000000000000000000000000030625000000000000000000000000023534235350000000000275342753527534275350000000000
010a00000000000000000000000030625000000000000000000000000028532285322853228532285322853228532285322853228535000000000030625000000000000000000000000030625000000000000000
010a00002353423535255342553500000000002553425535255342553500000000002253422535235342353223532235322353223532306250000000000000000013000135306250000000000000000013000135
010a00003062500000306250000000000000003062500000306250000000000000003062500000306150000000000000003061500000001300013000130001303062500000001300013000130001303062500000
010a000027534275352253422535000000000022534225352253422535000000000025534255351e5341e5321e5321e5321e5321e535306150000000000000000000000000306250000000000000000000000000
010a00000000000000306250000000000000000000000000306250000000000000000000000000306250000000000000000000000000235322353223532235322353223532235322353223532235322353223535
010a0000275342753227532275352a5342a5352a5342a5322a5322a5322a5322a532306250000000000000000313003135306250000000000000000613006135275342753227532275352a5342a5352353423532
010a00003062500000000000000030625000003061500000000000000030615000000313003130031300313030625000000613006130061300613030625000000813008130081300813030625000003061500000
010a00002a5342a5322a5322a53527534275352753427532275322753227532275353061500000000000000000000000003062500000000000000000000000002a5342a5322a5322a53527534275352753427532
010a00003062500000000000000000000000003062500000000000000000000000002a5322a5322a5322a5322a5322a5322a5322a5322a5322a5322a5322a5353062500000000000000008130081353062500000
010a000023532235352753427532306250000000000000000313003135306250000000000000000613006135275342753227532275352a5342a53530625000000000000000001300013530625000000000000000
010a00000000000000306150000003130031300313003130306250000006130061300613006130306250000008130081300813008130306250000000130001300013000130306150000000130001300013000130
010a00003062500000011300113001130011303062500000031300313003130031303062500000235342353500000000003061500000001300013000130001303062500000011300113001130011303062500000
010a00002a5322a5352a5342a53527534275350000000000285342853230625000000000000000011300113530625000000000000000001300013527534275322753227535275342753527534275350000000000
010a00000000000000306150000030615000000000000000306250000001130011300113001130306250000000130001300013000130306250000030615000000000000000306150000030615000000000000000
010a0000275322753527534275352a5342a535000000000025534255353062500000000000000000000000003062500000000000000000000000002a5342a5322a5322a5352a5342a5352a5342a5350000000000
010a00002a5342a535285342853228532285352853428535285342853500000000002553425535235342353223532235322353223532306250000000000000000013000135306250000000000000000013000135
010a00002753427535255342553225532255352553425535255342553500000000002853428535275342753227532275322753227535306150000000000000000000000000306250000000000000000000000000
010a00000000000000306250000000000000000000000000306250000000000000000000000000306250000000000000000000000000235322353223532235322353223532235322353223532235350000000000
001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00080008080100c0100e0100f02011020120201404015050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000900130b3400f33011320123201332015320153101631016310173101631016310153101432013320113200f3300c3400835003300000000000000000000000000000000000000000000000000000000000000
000700001d3502835032000205002050020500000002050000000205001e300000000730000000113000730000000000000000000000000000000000000000000000000000000000000000000000000000000000
__music__
01 00010203
00 04050607
00 14151617
00 18191a1b
00 1c1d1e1f
00 20212223
00 24252627
00 28290607
00 142a1617
00 18191a1b
00 2b2c2d1f
02 2e212f30

