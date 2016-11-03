# Methods for the Semidefinite interface

abstract AbstractSDModel <: AbstractMathProgModel
export AbstractSDModel

@define_interface begin
    SDModel
    setconstrB!
    setconstrentry!
    setobjentry!
end
