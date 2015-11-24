package wyvern.tools.typedAST.core.expressions;

import wyvern.target.corewyvernIL.FormalArg;
import wyvern.target.corewyvernIL.decl.Declaration;
import wyvern.target.corewyvernIL.decl.DefDeclaration;
import wyvern.target.corewyvernIL.decltype.DeclType;
import wyvern.target.corewyvernIL.decltype.DefDeclType;
import wyvern.target.corewyvernIL.expression.*;
import wyvern.target.corewyvernIL.expression.New;
import wyvern.target.corewyvernIL.support.GenContext;
import wyvern.target.corewyvernIL.type.ValueType;
import wyvern.target.corewyvernIL.type.StructuralType;
import wyvern.tools.errors.FileLocation;
import wyvern.tools.typedAST.abs.CachingTypedAST;
import wyvern.tools.typedAST.core.evaluation.Closure;
import wyvern.tools.typedAST.core.binding.NameBinding;
import wyvern.tools.typedAST.core.binding.NameBindingImpl;
import wyvern.tools.typedAST.interfaces.*;
import wyvern.tools.typedAST.interfaces.Value;
import wyvern.tools.typedAST.transformers.ExpressionWriter;
import wyvern.tools.typedAST.transformers.GenerationEnvironment;
import wyvern.tools.typedAST.transformers.ILWriter;
import wyvern.tools.types.Environment;
import wyvern.tools.types.Type;
import wyvern.tools.types.TypeResolver;
import wyvern.tools.types.extensions.Arrow;
import wyvern.tools.types.extensions.Unit;
import wyvern.tools.util.EvaluationEnvironment;
import wyvern.tools.util.TreeWriter;


import java.util.*;
import java.util.stream.Collectors;

public class Fn extends CachingTypedAST implements CoreAST, BoundCode {
	private List<NameBinding> bindings;
	TypedAST body;

	public Fn(List<NameBinding> bindings, TypedAST body) {
		this.bindings = bindings;
		this.body = body;
	}

	@Override
	public void writeArgsToTree(TreeWriter writer) {
		writer.writeArgs(bindings, body);
	}

	@Override
	protected Type doTypecheck(Environment env, Optional<Type> expected) {
		Type argType = null;
		for (int i = 0; i < bindings.size(); i++) {
			NameBinding bdgs = bindings.get(i);
			bindings.set(i, new NameBindingImpl(bdgs.getName(), TypeResolver.resolve(bdgs.getType(), env)));
		}

		if (bindings.size() == 0)
			argType = new Unit();
		else if (bindings.size() == 1)
			argType = bindings.get(0).getType();
		else
			// TODO: implement multiple args
			throw new RuntimeException("tuple args not implemented");
		
		Environment extEnv = env;
		for (NameBinding bind : bindings) {
			extEnv = extEnv.extend(bind);
		}

		Type resultType = body.typecheck(extEnv, expected.map(exp -> ((Arrow)exp).getResult()));
		return new Arrow(argType, resultType);
	}

	@Override
	public Value evaluate(EvaluationEnvironment env) {
		return new Closure(this, env);
	}

	@Override
	public List<NameBinding> getArgBindings() {
		return bindings;
	}

	@Override
	public TypedAST getBody() {
		return body;
	}

	@Override
	public void accept(CoreASTVisitor visitor) {
		visitor.visit(this);
	}

	@Override
	public Map<String, TypedAST> getChildren() {
		Hashtable<String, TypedAST> children = new Hashtable<>();
		children.put("body", body);
		return children;
	}

	@Override
	public void codegenToIL(GenerationEnvironment environment, ILWriter writer) {
		writer.write(new New(Arrays.asList(new DefDeclaration("call",
				bindings.stream().map(b->new FormalArg(b.getName(), (ValueType)b.getType().generateILType())).collect(Collectors.toList()),
                (ValueType)getType().generateILType(), ExpressionWriter.generate(iwriter->body.codegenToIL(new GenerationEnvironment(environment), iwriter)))), null, null));
	}

	@Override
	public TypedAST doClone(Map<String, TypedAST> nc) {
		return new Fn(bindings, nc.get("body"));
	}

	private FileLocation location = FileLocation.UNKNOWN;
	public FileLocation getLocation() {
		return this.location;
	}

	@Override
    /**
     * @param GenContext The type context of the lambda declaration
     * @return The Intermediate Representation of the inline function decl
     */
	public Expression generateIL(GenContext ctx) {
        /*
         * First, map the NameBindings to Formal Arguments, dropping the parameters into the IR.
         * Next, find the type of the body. The type of the body is the return type of the function.
         * This allows the creation of the DefDeclaration
         *
         * Next, create a new StructuralType, duplicating the DefDecl as a DeclType.
         * Use the StructualType and the DefDeclaration to make a New. Return.
         */

        // Extend the generalContext to include the parameters passed into the function.
        GenContext extendedCtx = ctx;
        for(NameBinding binding : this.bindings) {
            extendedCtx = extendedCtx.extend(
                binding.getName(),
                new wyvern.target.corewyvernIL.expression.Variable(binding.getName()),
                binding.getType().getILType(extendedCtx)
            );
        }

        List<FormalArg> intermediateArgs = convertBindingToArgs(this.bindings, extendedCtx);

        // Generate the IL for the body, and get it's return type.
        Expression il = this.body.generateIL(extendedCtx);
        ValueType bodyReturnType = il.typeCheck(extendedCtx);

        // Create a new list of function declaration, which is a singleton, containing only "apply"
        DefDeclaration applyDef = new DefDeclaration("apply", intermediateArgs, bodyReturnType, this.body.generateIL(extendedCtx));
        List<Declaration> declList = new LinkedList<>();
        declList.add(applyDef);

        // Store a redundency of the function declaration
        DeclType ddecl = new DefDeclType("apply", bodyReturnType, intermediateArgs);
        List<DeclType> declTypes = new LinkedList<>();
        declTypes.add(ddecl);

        ValueType newType = new StructuralType("lambda", declTypes);

        return new New(declList, "lambda", newType);
}

    private static List<FormalArg> convertBindingToArgs(List<NameBinding> bindings, GenContext ctx) {

        List<FormalArg> result = new LinkedList<FormalArg>();

        for(NameBinding binding : bindings) {
            result.add( new FormalArg(
                binding.getName(),
                binding.getType().getILType(ctx)
            ));
        }

        return result;
    }
}
