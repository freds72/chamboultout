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
local k_small,k_small_v=0.001,0.01
-- baumgarte
local k_bias=0.2
local k_slop=0.05

function lerp(a,b,t)
	return a*(1-t)+b*t
end
function smoothstep(t)
	t=mid(t,0,1)
	return t*t*(3-2*t)
end

-->8
-- physic engine
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
	local nimpulse=0
	local ra=make_v(a.pos,p)
	local racn=v_cross(ra,n)

	local nm=a.mass_inv
	nm+=v_dot(racn,m3_x_v(a.i_inv,racn))
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
		local dv,n=v_clone(a.v),v_clone(n)
		a.v=v_add(a.v,v_cross(a.omega,ra))

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
			m3_x_v(
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
 	-- model bounding box
	local vmin,vmax={32000,32000,32000},{-32000,-32000,-32000}
	for _,v in pairs(bbox.v) do
		vmin,vmax=v_min(vmin,v),v_max(vmax,v)
	end
	
	-- compute inertia tensor
	local size=v_sqr(make_v(vmin,vmax))
	local ibody=make_m3(size[2]+size[3],size[1]+size[3],size[1]+size[2])
	m_scale(ibody,a.mass/12)
	
	-- invert 
	local ibody_inv=m3_inv(ibody)
	-- 
	local g={0,-24*a.mass,0}
	local m=a.m
	local rb={
		i_inv=make_m3(),
		v=v_zero(),
		rot={
			m[1],m[2],m[3],
			m[5],m[6],m[7],
			m[9],m[10],m[11]
		},
		q=make_q(_sun_dir,rnd()),
		omega=v_zero(),
		mass_inv=1/a.mass,
		-- obj to world space
		pt_toworld=function(self,p)
			return v_add(m3_x_v(self.rot,p),self.pos)
		end,		
		-- world velocity
		pt_velocity=function(self,p)
			return v_add(v_cross(self.omega,make_v(self.pos,p)),self.v)
		end,
		incident_face=function(self,rn)
			-- world to local (normal)
			rn=m3_inv_x_v(self.rot,rn)
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
			self.omega=v_add(self.omega,m3_x_v(self.i_inv,v_cross(make_v(self.pos,p),f)))
		end,
		-- apply forces & torque for iteration
		prepare=function(self,dt)
			-- add gravity
			force=v_add(force,g)
		
			-- inverse inertia tensor
			self.i_inv=m3_x_m3(m3_x_m3(self.rot,ibody_inv),m3_transpose(self.rot))
	
			-- velocity
			self.v=v_add(self.v,force,self.mass_inv*dt)
	
			-- angular velocity
			self.omega=v_add(self.omega,m3_x_v(self.i_inv,torque),dt)
			
			-- friction
			v_scale(self.v,1/(1+dt*0.4))
			v_scale(self.omega,1/(1+dt*0.6))
		end,
		integrate=function(self,dt)
			self.pos=v_add(self.pos,self.v,dt)
			q_dydt(self.q,self.omega,dt)
			self.rot=m3_from_q(self.q)
			-- todo:
			local r=self.rot
			self.m={
				r[1],r[2],r[3],0,
				r[4],r[5],r[6],0,
				r[7],r[8],r[9],0,
				0,0,0,1
			}
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
		end
	}
end

-- clipping
function z_poly_clip(znear,v)
	local res,v0={},v[#v]
	local d0=v0[3]-znear
	for i=1,#v do
		local v1=v[i]
		local d1=v1[3]-znear
		if d1>0 then
			if d0<=0 then
				local nv=v_lerp(v0,v1,d0/(d0-d1))
				nv.x=64+((nv[1]/nv[3])<<6)
				nv.y=64-((nv[2]/nv[3])<<6)
				res[#res+1]=nv
			end
			res[#res+1]=v1
		elseif d0>0 then
			local nv=v_lerp(v0,v1,d0/(d0-d1))
			nv.x=64+((nv[1]/nv[3])<<6)
			nv.y=64-((nv[2]/nv[3])<<6)
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
		local a={ax,ay,az,outcode=outcode,clipcode=outcode&2,x=64+ax*w,y=64-ay*w,w=w}
		t[v]=a
		return a
	end
}

function collect_faces(model,m,out)
	-- cam pos in object space
	local cam_pos=m_inv_x_v(m,_cam.pos)
	-- sun vector in model space
	local sun=m_inv_x_n(m,_sun_dir)

	-- object to world
	-- world to cam
	-- vertex cache (and model context)
	local v_cache=setmetatable({m=m_x_m(_cam.m,m)},v_cache_cls)

	for _,face in pairs(model.f) do
		if v_dot(face.n,cam_pos)>face.cp then
			-- project vertices (always 4!!)
			local v0,v1,v2,v3=v_cache[face[1]],v_cache[face[2]],v_cache[face[3]],v_cache[face[4]]
			-- mix of near/far verts?
			if v0.outcode&v1.outcode&v2.outcode&v3.outcode==0 then
				local verts={v0,v1,v2,v3}

				local ni,is_clipped,w=9,v0.clipcode+v1.clipcode+v2.clipcode+v3.clipcode,v0.w+v1.w+v2.w+v3.w
				-- mix of near+far vertices?
				if(is_clipped>0) verts=z_poly_clip(z_near,verts)
				if #verts>2 then
					verts.f=face
					verts.light=mid(-v_dot(sun,face.n),0,1)
					-- sort key
					-- todo: improve
					verts.key=-w/4
					out[#out+1]=verts
				end
			end
		end
		::skip::
	end
end

-- draw face
function draw_faces(faces)
	for i,d in ipairs(faces) do
		-- todo: color ramp		
		polyfill(d,8+8*d.light)		
	end
end

function draw_ground()
    local out={}
	collect_faces(_ground.model,_ground.m,out)

    draw_faces(out)
end

function make_cube(mass,half_width,pos,rot)
	local model={
		hw=half_width,
		v={
			split"-1,-1,-1",
			split"1,-1,-1",
			split"1,-1,1",
			split"-1,-1,1",
			split"-1,1,-1",
			split"1, 1,-1",
			split"1, 1,1",
			split"-1, 1,1",
		},
		-- faces
		f={
			split"4,3,2,1",
			split"1,2,6,5",
			split"2,3,7,6",
			split"3,4,8,7",
			split"4,1,5,8",
			split"5,6,7,8"
		}
	}
	for _,v in pairs(model.v) do
		v_scale(v,half_width)
	end
	for _,f in pairs(model.f) do
		-- de-reference vertex indices
		for i=1,4 do
			f[i]=model.v[f[i]]
		end

		-- normal
		f.n=v_normz(
				v_cross(
					make_v(f[1],f[4]),
					make_v(f[1],f[2])))
		-- fast viz check
		f.cp=v_dot(f.n,f[1])
	end
	local m={unpack(rot)}
	m_set_pos(m,pos)
	return {
		mass=mass,
		hardness=0.02,
		model=model,
		pos=v_clone(pos),
		m=m
	}
end

-->8
-- game loop
function _init()
	-- capture mouse
	-- enable lock+button alias
	poke(0x5f2d,7)

	_cam=make_cam({0,25,-40})

	-- cube
	add(_things,make_rigidbody(make_cube(1,5,{0,50,0},make_m_from_euler(0,rnd(),0))))
	-- floor
	_ground=make_cube(0,50,{0,-50,0},make_m_from_euler(0,0,0))
end

function _update()
    world:update()
	_cam:update()
	time_t+=1
end

function _draw()
    cls()
	draw_ground()

    local out={}
	for _,thing in pairs(_things) do
		collect_faces(thing.model,thing.m,out)
	end

	sort(out)

    draw_faces(out)

	print(#out,2,2,7)
end

