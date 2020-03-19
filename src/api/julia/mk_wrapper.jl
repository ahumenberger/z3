using Clang
using Clang.LibClang

# ------------------------------------------------------------------------------

function compiler_preprocessor_verbose(compiler, flags)
    cmd = [compiler, "-E"] 
    append!(cmd, flags)
    append!(cmd, ["-", "-v"])
    err = Pipe()
    process = run(pipeline(Cmd(cmd); stdin=devnull, stdout=devnull, stderr=err))
    close(err.in)
    stderr = String(read(err))
    return split(stderr, "\n")
end

function system_include_paths(compiler::String)
    flags = ["-x", "c++"]
    lines = compiler_preprocessor_verbose(compiler, flags)
    lines = [strip(l) for l in lines]

    _start = findfirst(x->x=="#include <...> search starts here:", lines)
    _end   = findfirst(x->x=="End of search list.", lines)

    lines = lines[_start+1:_end-1]
    paths = String[]
    for line in lines
        line = replace(line, "(framework directory)"=>"")
        line = strip(line)
        push!(paths, line)
    end
    return paths
end

includes = system_include_paths("clang")
push!(includes, dirname(pwd()))

args = [
    "-x",
    "c++",
    "-std=c++11",
]

const CPP_FILE    = joinpath(dirname(pwd()), "c++", "z3++.h")
const TRANS_UNIT  = parse_header(CPP_FILE, args=args, includes=includes)
const ROOT_CURSOR = getcursor(TRANS_UNIT)
const Z3_CURSOR   = search(ROOT_CURSOR, x->kind(x)==CXCursor_Namespace && spelling(x)=="z3")[1]

# ------------------------------------------------------------------------------

EXCLUDED_CLASSES = [
    "exception",
    "cast_ast"
]

# ------------------------------------------------------------------------------

function SKIP(c::CLCursor, reason::String)
    @info "Skip ($(reason)) $(c)"
end

# ------------------------------------------------------------------------------

function write_wrapper(io::IO)
    write_header(io)
    println(io, "")
    write_supertypes(io, Z3_CURSOR)
    println(io, "")
    println(io, "JLCXX_MODULE define_julia_module(jlcxx::Module &$(module_obj()))\n{")
    write_classes(io, Z3_CURSOR)
    println(io, "")
    write_enums(io, Z3_CURSOR)
    println(io, "")
    write_custom(io)
    println(io, "")
    write_members(io, Z3_CURSOR)
    println(io, "")
    write_functions(io, Z3_CURSOR)
    println(io, "}")
end

function write_custom(io::IO)
    println(io, """
        $(module_obj()).add_type<jlcxx::Parametric<jlcxx::TypeVar<1>>>("AstVectorTpl")
        .apply<z3::ast_vector_tpl<z3::ast>, z3::ast_vector_tpl<z3::expr>, z3::ast_vector_tpl<z3::sort>, z3::ast_vector_tpl<z3::func_decl>>(
            [](auto wrapped) {
                typedef typename decltype(wrapped)::type WrappedT;
                wrapped.template constructor<z3::context &>();
                wrapped.module().set_override_module(jl_base_module);
                wrapped.method("length", &WrappedT::size);
                wrapped.method("getindex", [](const z3::model &x, int i) { return x[i - 1]; });
                wrapped.method("push!", &WrappedT::push_back);
                wrapped.method("string", [](const WrappedT &x) {
                    std::ostringstream stream;
                    stream << x;
                    return stream.str();
                });
                wrapped.module().unset_override_module();
            });
    """)
    add_custom_type!(search(Z3_CURSOR, "ast_vector_tpl")[1])
end

# ------------------------------------------------------------------------------

# ------------------------------------------------------------------------------

_custom_added_types = CLCursor[]
add_custom_type!(c::CLCursor) = push!(_custom_added_types, c)
custom_added_types() = _custom_added_types
custom_added_types_qualified() = map(qualified, custom_added_types())

# ------------------------------------------------------------------------------

const INDENT = "    "

wrapper_obj(class::String) = "w_$class"
julia_name(class::String) = join(map(uppercasefirst, split(class, "_")))
module_obj() = "m"
set_override() = "$(module_obj()).set_override_module(jl_base_module);"
unset_override() = "$(module_obj()).unset_override_module();"

FUNCTION_MAP = Dict{String, String}(
    "!"        => "not",
    "&&"       => "and",
    "||"       => "or",
    "function" => "fun"
)

julia_func_name(fn::String) = get(FUNCTION_MAP, fn, fn)


is_const_fn(cursor) = clang_CXXMethod_isConst(cursor) == 1

is_C_API(cursor) = startswith(spelling(cursor), "Z3_") || startswith(spelling(cursor), "_Z3_")

is_operator(cursor) = startswith(spelling(cursor), "operator")
function get_operator(cursor)
    @assert is_operator(cursor)
    spelling(cursor)[9:end]
end

# ------------------------------------------------------------------------------

function qualified(cursor)
    k = kind(cursor)
    if k == CXCursor_TranslationUnit
        return ""
    elseif !(cursor isa CLNoDeclFound)
        s = qualified(get_semantic_parent(cursor))
        if !isempty(s)
            return "$(s)::$(spelling(cursor))"
        end
    end
    return spelling(cursor)
end

function argstr(cursor)
    join([spelling(type(c)) for c in function_args(cursor)], ", ")
end

function retstr(cursor)
    t = result_type(cursor)
    return spelling(t)
end

function base_type(c::CLParmDecl)
    t = canonical(type(c))
    if t isa CLLValueReference
        return pointee_type(t)
    end
    return t
end

function get_type(m::CLCXXMethod)
    ret    = retstr(m)
    args   = argstr(m)
    consts = is_const_fn(m) ? " const" : ""
    class  = qualified(get_semantic_parent(m))
    return "$(ret) ($(class)::*)($(args))$(consts)"
end

function get_type(m::CLFunctionDecl)
    ret  = retstr(m)
    args = argstr(m)
    return "$(ret) (*)($(args))"
end

# ------------------------------------------------------------------------------

function is_type_wrapped(c::CLRecord)
    decl = typedecl(c)
    qual = qualified(decl)
    if startswith(qual, "z3")
        if is_wrappable(decl)
            return true
        elseif qual in custom_added_types()
            return true
        end
        return false
    end
    return true
end

is_type_wrapped(c::CLEnum) = is_wrappable(c)
is_type_wrapped(c::CLTypedef) = !is_C_API(c)
is_type_wrapped(c::CLType) = true

function is_type_wrapped(c::CLParmDecl)
    is_C_API(type(c)) && return false
    t = base_type(c)
    return is_type_wrapped(t)
end

function is_wrappable(cursor)
    if !all(is_type_wrapped(a) for a in function_args(cursor))
        SKIP(cursor, "Unwrapped argument type")
        return false
    end
    if !is_type_wrapped(result_type(cursor))
        SKIP(cursor, "Unwrapped return type")
        return false
    end
    return true
end
function is_wrappable(cursor::CLConstructor)
    if !all(is_type_wrapped(a) for a in function_args(cursor))
        SKIP(cursor, "Unwrapped argument type")
        return false
    end
    return true
end

is_wrappable(cursor::CLEnumDecl) = !is_C_API(cursor)
is_wrappable(cursor::CLEnum) = is_wrappable(typedecl(cursor))
is_wrappable(cursor::CLStructDecl) = is_C_API(cursor)

function is_wrappable(cursor::CLClassDecl)
    if spelling(cursor) in EXCLUDED_CLASSES
        SKIP(cursor, "Manually excluded")
        return false
    end
    return getdef(cursor) == cursor
end

# ------------------------------------------------------------------------------

function write_supertypes(io::IO, parent::CLCursor)
    println(io, "namespace jlcxx\n{")
    for c in search(parent, CXCursor_ClassDecl)
        cname = name(c)
        baseclasses = search(c, CXCursor_CXXBaseSpecifier)
        if length(baseclasses) == 1
            s = qualified(c)
            t = qualified(typedecl(type(baseclasses[1])))
            print(io, INDENT)
            println(io, "template<> struct SuperType<$(s)> { typedef $(t) type; };")
        elseif length(baseclasses) > 1
            @warn "Cannot handle more than one base class, skipping $(c)"
        end
    end
    println(io, "}")
end

function write_members(io::IO, parent::CLCursor)
    for c in search(parent, CXCursor_ClassDecl)
        !is_wrappable(c) && continue
        println(io, "")
        write_constructors(io, c)
        write_member_functions(io, c)
    end
end

function write_operator(io::IO, cursor)
    op = get_operator(cursor)
    argtypes = map(type, function_args(cursor))
    args = map(spelling, argtypes)
    if op == "<<"
        println(io,
            """
                $(set_override())
                $(module_obj()).method("string", []($(args[2]) x) {
                    std::ostringstream stream;
                    stream << x;
                    return stream.str();
                });
                $(unset_override())
            """
        )
    elseif op == "[]"
        if argtypes[1] isa CLInt
            class_cursor = get_semantic_parent(cursor)
            class = qualified(class_cursor)
            println(io,
                """
                    $(set_override())
                    $(module_obj()).method("getindex", [](const $(class) &x, int i) { return x[i - 1]; });
                    $(unset_override())
                """
            )
        else
            SKIP(cursor, "Non-integer type argument in operator[]")
        end
    elseif op == "()"
        func_name    = spelling(cursor)
        class_cursor = get_semantic_parent(cursor)
        class_name   = name(class_cursor)
        class        = qualified(class_cursor)
        func_type    = get_type(cursor)
        print(io, INDENT)
        println(io, "$(wrapper_obj(class_name)).method(static_cast<$(func_type)>(&$(class)::$(func_name)));")
    elseif op == "="
        SKIP(cursor, "Assignment operator not handled")
    else
        print(io, INDENT)
        jl_op = julia_func_name(op)
        if length(args) > 2
            SKIP(cursor, "More than two arguments")
            return
        end
        fn = if length(args) == 1
            "[]($(args[1]) a) { return $(op) a; })"
        elseif length(args) == 2
            "[]($(args[1]) a, $(args[2]) b) { return a $(op) b; })"
        end
        println(io, "$(module_obj()).method(\"$(jl_op)\", $(fn);")
    end
end

function write_member_functions(io::IO, class_cursor)
    class_name = name(class_cursor)
    for cursor in search(class_cursor, CXCursor_CXXMethod)
        if clang_getCXXAccessSpecifier(cursor) == CX_CXXPublic
            !is_wrappable(cursor) && continue
            if is_operator(cursor)
                write_operator(io, cursor)
            elseif clang_CXXMethod_isStatic(cursor) == 1
                SKIP(cursor, "Static functions not yet supported")
            else
                type    = get_type(cursor)
                name    = spelling(cursor)
                jl_name = julia_func_name(name)
                class   = qualified(class_cursor)
                print(io, INDENT)
                println(io, "$(wrapper_obj(class_name)).method(\"$(jl_name)\", static_cast<$(type)>(&$(class)::$(name)));")
            end
        end
    end
end

function write_constructors(io::IO, class_cursor)
    class = name(class_cursor)
    for cursor in search(class_cursor, CXCursor_Constructor)
        if clang_getCXXAccessSpecifier(cursor) == CX_CXXPublic
            !is_wrappable(cursor) && continue
            print(io, INDENT)
            println(io, "$(wrapper_obj(class)).constructor<$(argstr(cursor))>();")
        end
    end
end

function write_functions(io::IO, cursor)
    for fncursor in search(cursor, CXCursor_FunctionDecl)
        !is_wrappable(fncursor) && continue
        if is_operator(fncursor)
            write_operator(io, fncursor)
        else
            name    = spelling(fncursor)
            jl_name = julia_func_name(name)
            func    = qualified(fncursor)
            type    = get_type(fncursor)
            print(io, INDENT)
            println(io, "$(module_obj()).method(\"$(jl_name)\", static_cast<$(type))>(&$(func)));")
        end
    end
end

function write_header(io::IO)
    println(io, """
    #include "jlcxx/jlcxx.hpp"
    #include "z3++.h"
    """)
end

function write_classes(io::IO, parent::CLCursor)
    for c in search(parent, CXCursor_ClassDecl)
        !is_wrappable(c) && continue
        baseclasses = search(c, CXCursor_CXXBaseSpecifier)
        if length(baseclasses) > 1
            SKIP(c, "More than one base classes")
            continue
        end
        class = qualified(c)
        name  = spelling(c)
        if length(baseclasses) == 0
            base = ""
        else
            base = qualified(typedecl(type(baseclasses[1])))
            base = ", jlcxx::julia_base_type<$(base)>()"
        end
        print(io, INDENT)
        println(io, "jlcxx::TypeWrapper<$(class)> $(wrapper_obj(name)) = $(module_obj()).add_type<$(class)>(\"$(julia_name(name))\"$(base));")
    end
end

function write_enums(io::IO, parent::CLCursor)
    for c in search(parent, CXCursor_EnumDecl)
        !is_wrappable(c) && continue
        name    = spelling(c)
        jl_name = julia_name(name)
        print(io, INDENT)
        println(io, "$(module_obj()).add_bits<$(name)>(\"$(jl_name)\", jlcxx::julia_type(\"CppEnum\"));")
        for ch in children(c)
            name = spelling(ch)
            print(io, INDENT)
            println(io, "$(module_obj()).set_const(\"$(name)\", $(name));")
        end
    end
end

open("z3jl.cpp", "w") do io
    write_wrapper(io)
end