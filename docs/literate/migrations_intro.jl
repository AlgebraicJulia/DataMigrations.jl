# # Introduction to Data Migrations

# DataMigrations.jl includes facilities for categorical data migrations. 
# We'll start by example, working with some graph schemas from Catlab.

using Catlab, DataMigrations
M = @migration SchReflexiveGraph SchGraph begin
  V => V
  E => @cases begin e::E; v::V end
  src => begin e => src; v => id(V) end
  tgt => begin e => tgt; v => id(V) end
  refl => v
end

# This is a migration from `SchReflexiveGraph` to `SchGraph`.
# Every call to `@migration` constructs a *contravariant*
# data migration, which means in this case that `M` will 
# turn graphs into reflexive graphs. 
# To construct `M`, we construct a functor whose domain
# is `SchReflexiveGraph`. The codomain is not just `SchGraph`,
# though! Before we get into that, let's understand what the 
# syntax is signifying more concretely.

# In general, each assignment statement `a => b` means
# "when I migrate a graph `G` to a reflexive graph `H` with this
# migration, I want the `a` in `H` to be given by `b`." 
# `b` will be some expression that makes sense in terms of the
# *original* graph `G`.

# Thus the first line `V => V` is easy: we want the vertices of `H`
# to be the same as the vertices of `G`. For the second line,
# `E => @cases begin e::E; v::V end`,
# things begin to get interesting. What this is saying is that we 
# want an *edge* in `H` to be *either* an edge in `G` *or* a vertex
# in `G`. Thus both `E` and `V` refer to those sorts for `G`. 
# The little `e` and `v` function as references for later.

# Next we have to define our migration on the homs in `SchReflexiveGraph`.
# The line 
# `src => begin e => src; v => id(V) end`
# says that we want the `src` function in our new reflexive graph `H` to 
# be given by sending an edge to its original `src` and a vertex to itself.
# The `tgt` function of `H` behaves much the same. 
# Finally, we need `refl` to be a function from `H`'s `V` to `H`'s `E`, 
# and the only likely way to do that is to send a vertex to itself via `v`. 
# (So you can think of `e` and `v` as the two inclusions into the coproduct,
# if you like.)

# All in all, what have we done? Let's give it a try!
G = Graph(3)
H = migrate(ReflexiveGraph,G,M)
# We see that `M` takes the discrete graph on 3 vertices to the discrete
# reflexive graph on 3 vertices; that is, `M` just adds a new loop to each
# vertex. And there's our first data migration!

# That was an example of a *colimit* migration, in that in involved 
# building a disjoint union, i.e. coproduct. Let's now look at an example
# of a limit migration. And why not make things look a bit more practical?
# Here's a schema for some tasks and workers, where we can assign times 
# for a job to be done and a worker who's supposedly going to do that job
# at that time.

@present SchSchedule(FreeSchema) begin 
  Jobs::Ob
  Workers::Ob
  assignment::Hom(Jobs,Workers)

  Time::AttrType
  time::Attr(Jobs,Time)
end
@acset_type Schedule(SchSchedule,index = [:assignment])

# Now let's construct a simple migration to find jobs assigned to the same 
# worker at the same time. 

@present SchConflicts(FreeSchema) begin
  ConflictedPairs::Ob
  Job1::Ob
  Job2::Ob
  Workers::Ob
  assignment::Hom(ConflictedPairs,Workers)
  job1::Hom(ConflictedPairs,Job1)
  job2::Hom(ConflictedPairs,Job2)

  Time::AttrType
  time::Attr(ConflictedPairs,Time)
end
@acset_type Conflicts(SchConflicts,index = [:assignment])

# The key thing is going to be to construct the set of conflicted pairs:
# pairs (x,y) of jobs assigned to the same worker at the same time. 
# This is a perfect job for a *limit* migration.

N = @migration SchConflicts SchSchedule begin 
  ConflictedPairs => @join begin
                      X::Jobs
                      Y::Jobs
                      W::Workers
                      T::Time
                      (a:X→W)::assignment
                      (b:Y→W)::assignment
                      (t:X→T)::time
                      (s:Y→T)::time
  end
  Job1 => Jobs
  Job2 => Jobs
  Workers => Workers
  assignment => assignment(X)
  job1 => X
  job2 => Y
  Time => Time
  time => time(X)
end

# Most of this migration is easy enough, but the image of `ConflictedPairs``
# is quite complicated. We've specified a *diagram* in `SchSchedule`,
# given by mapping the graph with vertices `X,Y,W,T` and edges 
# `a,b,t,s` into that schema according to the mapping given to the right of
# the double colons.

# What the `@join` decoration does is instruct the migration to send a `Schedule`
# `A` to a `Conflicts` `B` whose `ConflictedPairs` are the set of all ways to 
# choose an element of `A`'s `Jobs` for `X` and for `Y`, an element of 
# `A`'s `Workers` for `W`, and an element of `A`'s `Time` for `T`, in such a
# way that moving along any of the four edges sends one of the selected choices to
# another. What this amounts to is, as promised, all the ways to choose two jobs
# assigned the same worker and the same time. Let's see it in action. We'll 
# use Julia's `Time` type for the `Time` attribute but for now, times will be on 
# whole hours.
using Dates
A = @acset Schedule{Time} begin
  Jobs = 7
  Workers = 3
  assignment = [1,3,2,2,3,1,1]
  time = Time.([9,9,10,11,10,10,9])
end

# You can probably spot that we ought to get one conflict, since worker 1 
# is supposed to be doing both jobs 1 and 7 at 9:00am. Let's check:

A′ = migrate(Conflicts,A,N)
