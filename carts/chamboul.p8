pico-8 cartridge // http://www.pico-8.com
version 33
__lua__
-- chamboultout
-- by @freds72
-- physic code by: Randy Gaul
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
		add=function(self,a)
			local bbox=a.model
			local force,torque=v_zero(),v_zero()
			local is_static=false

			-- compute (inverse) inertia tensor
			local ibody_inv
			if a.mass>0 then
				local ex,ey,ez=unpack(a.extents)
				-- 4=square(2*extents)
				local size={4*ex*ex,4*ey*ey,4*ez*ez}
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
			local g={0,-24*a.mass,0}
			local rb={
				id=_id,
				-- special case for ground :/
				radius=a.extents and v_len(a.extents) or 0,
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
					force=v_add(force,f,self.mass/a.hardness)
					torque=v_add(torque,v_cross(make_v(self.pos,p),f),a.friction)
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
			for k,c in pairs(contacts) do
				if(c.ttl>0) c.ttl-=1
			end

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
						local ct=contacts[pid] or {a=a,b=b,ttl=0}
						if ct.ttl==0 then
							sfx(rnd{8,9,10})
							-- (re)register
							contacts[pid]=ct
						end
						ct.ttl=5

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
			if(btn(0,1)) dx=1
			if(btn(1,1)) dx=-1
			if(btn(2,1)) dz=1
			if(btn(3,1)) dz=-1

			dangle=v_add(dangle,{stat(39),stat(38),dx/4})
			angle=v_add(angle,dangle,1/1024)
			
			local c,s=cos(a),-sin(a)
			velocity=v_add(velocity,{s*dz-c*dx,0,c*dz+s*dx}) 	
			
			-- check next position
			local vn,vl=v_normz(velocity)      
			if vl>0.1 then
				local next_pos=v_add(self.pos,velocity)
				local vel2d=v_normz({vn[1],0,vn[3]})
				-- check current to target pos
				for i=1,3 do
					local hit=hitscan(_things,self.pos,next_pos,2)
					if hit then
						local n=hit.face.n
						local fix=v_dot(n,velocity)
						-- separating?
						if fix<0 then
							velocity=v_add(velocity,n,-fix)
						end
						next_pos=v_add(self.pos,velocity)
					else
						goto clear
					end
				end
				-- cornered?
				velocity={0,0,0}
		::clear::
			else
				velocity={0,0,0}
			end

			local pos=v_add(self.pos,velocity)

			-- update rotation
			local m=make_m_from_euler(unpack(angle))	
			-- inverse view matrix
			self.m=make_inv_transform(m,pos)
            self.pos=pos

			local m=make_m_from_euler(-angle[1],angle[2],angle[3])	
            --
            self.m_mirror=m_x_m(m3_transpose(m),{
				1,0,0,0,
				0,1,0,0,
				0,0,1,0,
				-pos[1],pos[2],-pos[3],1
			})
            self.pos_mirror={pos[1],-pos[2],pos[3]}
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
		local outcode=k_near
		if(az>z_near) outcode=k_far
		if(ax>az) outcode+=k_right
		if(-ax>az) outcode+=k_left

		-- not faster :/
		-- local bo=-(((az-z_near)>>31)<<17)-(((az-ax)>>31)<<18)-(((az+ax)>>31)<<19)
		-- assert(bo==outcode,"outcode:"..outcode.." bits:"..bo)

		-- assume vertex is visible, compute 2d coords
		local w=64/az
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
						local w=64/v[3]
						v.x=64+v[1]*w
						v.y=64-v[2]*w
						key+=w
					end
					verts.face=face
					verts.uvs=uvs
					verts.light=mid(-face.sign*sun[face.axis],-1,1)
					-- sort key
					-- todo: improve
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

	for i,d in ipairs(faces) do
		-- todo: color ramp	
		--fillp()
		--if(not d.visible) fillp(0xa5a5.8)
		--pal(_dithers[flr(12*(1-d.light))],2)
		if mirror then			
			polyfill(d,0x7d)			
		else
			local base=_dithers[flr(6+6*d.light)]
			pal(base,2)
			if d.uvs then				
				tpoly(d,d.uvs)
			else
				polyfill(d,base[d.model.color])
			end
			--if(hits and hits.reference_face==d.face) polyfill(d,11)
			--if(hits and hits.incident_face==d.face) polyfill(d,8)
			--polyline(d,5)--d.thing.sleeping and 11 or 12)			
		end
	end
	--if hits then
	--	for _,v in pairs(hits.contacts) do
	--		local x0,y0,w0=_cam:project2d(v)
	--		if(w0) circfill(x0,y0,2,2)
	--	end
	--end
end

function draw_ground()
	-- texture coords
	poke(0x5f38,4)
	poke(0x5f39,4)
	poke(0x5f3a,8)
	poke(0x5f3b,0)

	-- todo: optimize for tokens
	local sun=v_add(_cam.pos,_sun_dir,-16)
	local x0,y0,w0=_cam:project2d(sun)
	if w0 then
		fillp(0xa5a5)
		circfill(x0,y0,12,0x7c)
		fillp()
		circfill(x0,y0,10,7)
	end
	local sun=v_add(_cam.pos,{0,0.707,0.707},-16)
	x0,y0,w0=_cam:project2d(sun)
	if w0 then
		fillp(0xf0f0.8)
		circfill(x0,y0,12,0x7d)
		fillp()
	end

	local m=_cam.m
	local fwd,up,right=
		{m[3],m[7],m[11]},
		{m[2],m[6],m[10]},
		{m[1],m[5],m[9]}
	local x,y,z=unpack(_cam.pos)
	local scale=4
	local horiz=32000
	for i=127,0,-1 do
		local vu=v_add(fwd,up,(64-i)/64)
		-- vector toward ground?
		if (vu[2]<-k_small) then 
			horiz=i
			local vl=v_add(vu,right,-1)    -- left ray
			local vr=v_add(vu,right, 1)    -- right ray

			-- y=0 intersection
			local kl,kr=-y/vl[2],-y/vr[2]

			local tx,tz=vl[1]*kl+x,vl[3]*kl+z
			--rectfill(-64,i,64,i,8)
			tline(0,i,127,i,tx>>2,tz>>2,(vr[1]*kr+x-tx)>>9,(vr[3]*kr+z-tz)>>9)
		end
	end
	--rectfill(0,horiz-2,128,horiz-2,7)
	--rectfill(0,horiz-1,128,horiz-1,5)
	--rectfill(0,horiz,128,horiz,6)

	poke4(0x5f38, 0)
end

function make_box(mass,extents,pos,q,uvs)
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
		color=4,
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
			if i==1 or i==6 then
				f.uv={
					{mx,my+2*ez},
					{mx+2*ex,my+2*ez},
					{mx+2*ex,my},
					{mx,my}
				}
				mx+=2*ex
			end
			if i==2 or i==4 then
				f.uv={
					{mx,my+2*ey},
					{mx+2*ex,my+2*ey},
					{mx+2*ex,my},
					{mx,my}
				}
				mx+=2*ex
			end
			if i==3 or i==5 then
				f.uv={
					{mx,my+2*ey},
					{mx+2*ez,my+2*ey},
					{mx+2*ez,my},
					{mx,my}
				}
				mx+=2*ez
			end
		end
	end

	-- initial condition
	local m=m_from_q(q)
	m_set_pos(m,pos)

	return {
		mass=mass,
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
		friction=0.4,
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

	_cam=make_cam({0,5,-20})
	_scene=make_scene()

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
	--[[
	for _,q in pairs(pins) do
		add(_pins,
			add(_things,			
				_scene:add(make_box(
					1,{2,6,2},
					{q[1],3,q[3]},
					--make_q(v_normz({rnd(),rnd(),rnd()},rnd()))
					make_q(v_up,rnd())
				))
			))
	end
	]]

	local deers={
		{0,0,-9},
		{4,0,9},
		{-4,0,9}
	}
	for _,p in pairs(deers) do
		add(_things,
			_scene:add(
				make_box(
					0,{3,6,7},
					{p[1],3,p[3]},
					--make_q(v_normz({rnd(),rnd(),rnd()},rnd()))))
					make_q(v_up,0.125-rnd(0.25)),
					{mx=0,my=0,[2]=true,[4]=true})))
	end

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

local _fire_ttl=0

function _update()
	_cam:update()
	
	_fire_ttl-=1
	if _fire_ttl<0 and btnp(4) then
		_fire_ttl=30
		local m=_cam.m
		local b=add(_things,			
			_scene:add(make_box(
				1,{2,2,2},
				v_add(_cam.pos,{1,3,0}),
				make_q(v_normz({rnd(),rnd(),rnd()},rnd())),
				{mx=0,my=8,1,2,3,4,5,6}
				)
			))
		b:add_force({128*m[3],96*m[7],128*m[11]},b.pos)
		--[[
		add(_particles,{
			pos=v_clone(_cam.pos),
			v={m[3],m[7],m[11]},
			ttl=90+rnd(30)
		})
		]]
	end

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

	-- 
	for _,p in pairs(_pins) do
		if (not p.on_ground) and p.sleeping then
			local up=m_row(p.m,2)
			if abs(up[2])<0.98 then
				p.on_ground=true
			end
		end
	end
end

function _draw()
    cls(12)

	-- mirror image
    local out,mirror_cam={},{pos=_cam.pos_mirror,m=_cam.m_mirror,flip=true}
	for _,thing in pairs(_things) do
		collect_faces(mirror_cam,thing,thing.model,thing.m,out)
	end

    draw_faces(out,true)

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

	for _,p in pairs(_particles) do
		local x0,y0,w0=_cam:project2d(p.pos)
		if w0 then
			circfill(x0,y0,w0,6)
			circ(x0,y0,w0,7)
		end
	end
end

__gfx__
000000008888888a777777777777777777777777444444444444444444444444077000000077070000000000000770778888888aa88888880000000000000000
111111118888888a7776666776666777777777774444444444444444774444777770000000707077000000000000077788aaa88aa88aaa880000000000000000
11222ee78888888a776000077000067777777777444444444444444477444477077000000070777000000000000000078aa8aa8aa8aa8aa80000000000000000
1533bba78888888a770000077000007777777777777777774444444477444477777000000070770000000000000000078a888aaaaaa888a80000000000000000
2444499a8888888a770000077000007777777777000000004444444470444407700000000077070000007700000000078aa888aaaa888aa80000000000000000
115566778888888a7700000770000077777777770000000044444444704444077000070000777000000770000000000788aa88aaaa88aa880000000000000000
155667778888888a77000007700000777777777700000000444444444444444470000777707700000007700000000007888aaaaaaaaaa8880000000000000000
55667777aaaaaaaa77777777777777777777777700000000444444444444444477700077777000000000000000000077aaaaaaaaaaaaaaaa0000000000000000
128888e7aaaaaaaa77777777777777771111111144277244444444424888888477770777007700000000000000000777aaaaaaaaaaaaaaaa0000000000000000
22499fa78888888a77777777777777771111111144277244444444429888888977777777777700000000000007707777888aaaaaaaaaa8880000000000000000
299aaa778888888a7777777777777777111111114427724444444442998888997077777777777000000000007777777788aa88aaaa88aa880000000000000000
5533bb778888888a777777777777777711111111444224444444444299999999770000777777000000000000000777778aa888aaaa888aa80000000000000000
155dccc78888888a777777a99a77777711111111444444444444444299999999770000077000000000000000000077778a888aaaaaa888a80000000000000000
11dd66778888888a77777a9999a7777711111111444444444444444444444444700000000000000000000000000007778aa8aa8aa8aa8aa80000000000000000
222eeff78888888a7777799999977777111111114444444444444444444444447000000000000000000000000000077788aaa88aa88aaa880000000000000000
22eeff778888888a777774999947777711111111444444444444444444444444000000000000000000000000000000708888888aa88888880000000000000000
00000000a88888887777774444777777444444447777777766446644944944947000000077700000000007777000007700000000000000000000000000000000
00000000a88888887777777777777777444444447777777766446644494949440000000077770000007777777770000700000000000000000000000000000000
00000000a88888887777777777777777440440447777777766446644449994440000007777770000007777777770000000000000000000000000000000000000
00000000a88888887777777777777700444004447777777766666644444944440000007777700000077777777777000000000000000000000000000000000000
00000000a88888887007777777777700444004447777777766666644944944940000007777770000000077777777000000000000000000000000000000000000
00000000a88888887007777777777777440440447777777744446644494949440000070777700000000770777777000000000000000000000000000000000000
00000000a88888887777007700770077444444444777777444446644449994440077777777000000007707777700000000000000000000000000000000000000
00000000aaaaaaaa7777007700770077444444444444444444446644444944440770777700000000000000777777000000000000000000000000000000000000
00000000aaaaaaaa7777777777777777000000004444444444664466444444440707707770000000077777777707000000000000000000000000000000000000
00000000a88888887777777777777777000000004444222244664466222244447770777777000000000777777707000000000000000000000000000000000000
00000000a88888887777777777777777000000004442222244664466222224447770077777700000077077007777700700000000000000000000000000000000
00000000a88888887777777777777777000000004442222244666666222224447770077777700077777777777777000700000000000000000000000000000000
00000000a88888886777777777777777000000004442222244666666222224447700007777777770777777777770777700000000000000000000000000000000
00000000a88888886777777777777776000000004442222244664444222224447777000007777770770000777777777700000000000000000000000000000000
00000000a88888886667777777777766000000004444222244664444222244447777000000707777770000007777777700000000000000000000000000000000
00000000a88888886666777777777666000000004444444444664444444444447770000000770777700000000007777700000000000000000000000000000000
__map__
260636060606000008090a0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
350737060606000018191a1b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
061706062506000028292a2b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
062506060606000038393a3b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0606060606060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0514050514050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
012101210121012101210c0d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
113111311131113111311c1d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
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
