# wrapper to convert SD solver into Conic solver

# To enable Conic support from an SD solver, define, e.g.,
# ConicModel(s::CSDPSolver) = SDtoConicBridge(SDModel(s))

type SDtoConicBridge <: AbstractConicModel
    sdmodel::AbstractSDModel
    varmap
    constrmap
    constrscaling
    c
    A
    b
    constr_cones
    var_cones
end

# FIXME implements supportedcones

SDtoConicBridge(m::AbstractSDModel) = SDtoConicBridge(m, nothing, nothing, nothing, nothing, nothing, nothing, nothing, nothing)

export SDtoConicBridge

numvar(m::SDtoConicBridge) = size(m.A,2)
numconstr(m::SDtoConicBridge) = size(m.A,1)

function getmatdim(k)
    # n*(n+1)/2 = k
    # n^2+n-2k = 0
    # (-1 + sqrt(1 + 8k))/2
    n = (-1 + sqrt(1 + 8k)) / 2
    if n * (n+1) != 2*k
        error("sd dim not consistent")
    end
    convert(Int, n)
end

# To transform Conic problems into SD problems
function loadproblem!(model::SDtoConicBridge, c, A, b, constr_cones, var_cones)
    m, n = size(A)
    model.c = c
    model.A = A
    model.b = b
    model.constr_cones = constr_cones
    model.var_cones = var_cones

    # Conic form        LP form
    # min  c'x          min      c'x
    #  st b-Ax ∈ K_1     st lb <= Ax <= b
    #        x ∈ K_2         l <=  x <= u

    # If a cone is anything other than [:Free,:Zero,:NonNeg,:NonPos,:SOC,:SDP], give up.
    bad_cones = [:ExpPrimal, :ExpDual, :SOCRotated]
    for (cone,_) in var_cones
        cone in bad_cones && error("Cone type $(cone) not supported")
    end
    for (cone,_) in constr_cones
        cone in bad_cones && error("Cone type $(cone) not supported")
    end

    blk = 0
    blkdims = Int[]
    socblks = Int[]
    # For a variable at column index `col' in the conic model,
    # varmap[col] gives an array such that each coefficient A[.,col] should be replaced by the sum,
    # over each element (blk, i, j, coef) of the array of
    # X[blk][i,j] * (A[.,col] * coef)
    # Where X[blk] is the blk'th block of X
    model.varmap = varmap = Vector{Vector{Tuple{Int,Int,Int,Float64}}}(n)
    for (cone,idxs) in var_cones
        # If a cone is anything other than [:Free,:Zero,:NonNeg,:NonPos,:SOC,:SDP], give up.
        if cone == :Free
            for i in idxs
                blk += 2
                push!(blkdims, 1)
                push!(blkdims, 1)
                # x free transformed into x = y - z with y, z >= 0
                varmap[i] = [(blk-1,1,1,1.), (blk,1,1,-1.)]
            end
        elseif cone == :Zero
            for i in idxs
                varmap[i] = []
            end
        elseif cone == :NonNeg
            for i in idxs
                blk += 1
                push!(blkdims, 1)
                varmap[i] = [(blk,1,1,1.)]
            end
        elseif cone == :NonPos
            for i in idxs
                blk += 1
                push!(blkdims, 1)
                varmap[i] = [(blk,1,1,-1.)]
            end
        elseif cone == :SOC
            blk += 1
            push!(blkdims, length(idxs))
            for i in 1:length(idxs)
                varmap[idxs[i]] = [(blk,1,i,-1.)]
            end
            push!(socblks, blk)
        elseif cone == :SDP
            d = getmatdim(length(idxs))
            k = 0
            blk += 1
            push!(blkdims, d)
            for i in 1:d
                for j in i:d
                    k += 1
                    # In the MPB conic model, those are scaled by sqrt(2)
                    coef = i == j ? 1. : 1/sqrt(2)
                    varmap[idxs[k]] = [(blk,i,j,coef)]
                end
            end
        else
            throw(ArgumentError("Unrecognized cone $cone"))
        end
    end
    @assert blk == length(blkdims)
    constr = 0
    # For the constraint at row index `row' in the conic model,
    # constrmap[row] gives the index of the constraint in the SD model,
    # a value of 0 meaning that it does not correspond to any constraint
    model.constrmap = constrmap = Vector{Int}(m)
    constrmapcheck = IntSet()
    # slackmap[row] gives (blk,i,j,coef) indicating that a slack variable has been created at X[blk][i,j] with coefficient coef
    # blk=0 corresponds to no slack
    slackmap = Vector{Tuple{Int,Int,Int,Float64}}(m)
    model.constrscaling = constrscaling = ones(Float64, m)
    for (cone,idxs) in constr_cones
        if cone == :Free
            for idx in idxs
                push!(constrmapcheck, idx)
            end
            constrmap[idxs] = 0
            slackmap[idxs] = 0
        else
            for idx in idxs
                constr += 1
                push!(constrmapcheck, idx)
                constrmap[idx] = constr
            end
            if cone == :Zero
                slackmap[idxs] = (0,0,0,0.)
            elseif cone == :NonNeg
                for idx in idxs
                    blk += 1
                    push!(blkdims, 1)
                    slackmap[idx] = (blk,1,1,1.)
                end
            elseif cone == :NonPos
                for idx in idxs
                    blk += 1
                    push!(blkdims, 1)
                    slackmap[idx] = (blk,1,1,-1.)
                end
            elseif cone == :SOC
                blk += 1
                push!(blkdims, length(idxs))
                varmap[idxs[1]] = [(blk,1,1,-1.)]
                for i in 1:length(idxs)
                    slackmap[idxs[i]] = (blk,1,i,1.)
                end
                push!(socblks, blk)
            elseif cone == :SDP
                d = getmatdim(length(idxs))
                k = 0
                blk += 1
                push!(blkdims, d)
                for i in 1:d
                    for j in i:d
                        k += 1
                        slackmap[idxs[k]] = (blk,i,j,i == j ? 1. : .5)
                        if i != j
                            constrscaling[idxs[k]] = 1/sqrt(2)
                        end
                    end
                end
            else
                throw(ArgumentError("Unrecognized cone $cone"))
            end
        end
    end
    if constrmapcheck != IntSet(1:m)
        throw(ArgumentError("Some variable have no cone"))
    end
    @assert blk == length(blkdims)

    socconstr = Vector{Int}(length(socblks))
    for i in 1:length(socblks)
        blk = socblks[i]
        n = blkdims[blk]
        socconstr[i] = constr
        constr += div(n*(n-1), 2)
    end

    # Writing the sparse block diagonal matrices
    # FIXME, why am I writting zeros ????
    sdmodel = model.sdmodel
    loadproblem!(sdmodel, blkdims, constr)
    for row in 1:m
        if constrmap[row] != 0
            setconstrB!(sdmodel, b[row] * constrscaling[row], constrmap[row])
        end
        blk, i, j, coef = slackmap[row]
        if blk != 0
            @assert coef != 0
            setconstrentry!(sdmodel, coef, constrmap[row], blk, i, j)
        end
    end
    if isa(A, SparseMatrixCSC)
        rows = rowvals(A)
        vals = nonzeros(A)
        for col in 1:n
            for k in nzrange(A, col)
                row = rows[k]
                if constrmap[row] != 0 # Free constraint
                    val = vals[k]
                    for (blk, i, j, coef) in varmap[col]
                        @assert coef != 0
                        setconstrentry!(sdmodel, val*coef*constrscaling[row], constrmap[row], blk, i, j)
                    end
                end
            end
        end
    else
        for col in 1:n
            for row in 1:m
                if constrmap[row] != 0
                    val = A[row,col]
                    for (blk, i, j, coef) in varmap[col]
                        @assert coef != 0
                        setconstrentry!(sdmodel, val*coef*constrscaling[row], constrmap[row], blk, i, j)
                    end
                end
            end
        end
    end
    for i in 1:length(socblks)
        c = socconstr[i]
        blk = soccblks[i]
        for i in 2:n
            for j in i:n
                c += 1
                setconstrB!(sdmodel, 0, c)
                setconstrentry!(sdmodel, 1., c, blk, i, j)
                if i != j
                    setconstrentry!(sdmodel, -1., c, blk, 1, 1)
                end
            end
        end
    end
    for col in 1:n
        if c[col] != 0
            for (blk, i, j, coef) in varmap[col]
                # in SDP format, it is max and in MPB Conic format it is min
                setobjentry!(sdmodel, -coef*c[col], blk, i, j)
            end
        end
    end
end

for f in [:optimize!, :status]
    @eval $f(model::SDtoConicBridge) = $f(model.sdmodel)
end

function getobjval(model::SDtoConicBridge)
    -getobjval(model.sdmodel)
end

function getsolution(model::SDtoConicBridge)
    X = getsolution(model.sdmodel)
    n = size(model.A, 2)
    x = zeros(Float64, n)
    for col in 1:n
        for (blk, i, j, coef) in model.varmap[col]
            x[col] += X[blk][i,j] / coef
        end
    end
    x
end

function getdual(model::SDtoConicBridge)
    y = getdual(model.sdmodel)
    constrmap = model.constrmap
    constrscaling = model.constrscaling
    m = size(model.A, 1)
    dual = Vector{Float64}(m)
    for row in 1:m
        if constrmap[row] != 0
            dual[row] = y[constrmap[row]] * constrscaling[row]
        else
            dual[row] = 0
        end
    end
    dual
end

function getvardual(model::SDtoConicBridge)
    Z = getvardual(model.sdmodel)
    n = size(model.A, 2)
    z = zeros(Float64, n)
    for col in 1:n
        for (blk, i, j, coef) in model.varmap[col]
            z[col] += Z[blk][i,j] / coef
        end
    end
    z
end

function getvartype(model::SDtoConicBridge, col)
    # they are all supposed to be the same so we take the first one
    blk, i, j, _ = first(model.varmap[col])
    getvartype(model.sdmodel, blk, i, j)
end

function setvartype!(model::SDtoConicBridge, vtype)
    for (col, vt) in enumerate(vtype)
        for (blk, i, j, _) in model.varmap[col]
            setvartype!(model.sdmodel, vt, blk, i, j)
        end
    end
end

for f in SolverInterface.methods_by_tag[:rewrap]
    @eval $f(model::SDtoConicBridge) = $f(model.sdmodel)
end
