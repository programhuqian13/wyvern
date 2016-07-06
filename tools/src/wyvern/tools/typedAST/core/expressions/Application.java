package wyvern.tools.typedAST.core.expressions;

import static wyvern.tools.errors.ErrorMessage.TYPE_CANNOT_BE_APPLIED;
import static wyvern.tools.errors.ErrorMessage.VALUE_CANNOT_BE_APPLIED;
import static wyvern.tools.errors.ToolError.reportError;
import static wyvern.tools.errors.ToolError.reportEvalError;

import java.util.Arrays;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import wyvern.stdlib.Globals;
import wyvern.target.corewyvernIL.FormalArg;
import wyvern.target.corewyvernIL.decl.TypeDeclaration;
import wyvern.target.corewyvernIL.decltype.AbstractTypeMember;
import wyvern.target.corewyvernIL.decltype.DefDeclType;
import wyvern.target.corewyvernIL.expression.Expression;
import wyvern.target.corewyvernIL.expression.MethodCall;
import wyvern.target.corewyvernIL.expression.Variable;
import wyvern.target.corewyvernIL.support.CallableExprGenerator;
import wyvern.target.corewyvernIL.support.GenContext;
import wyvern.target.corewyvernIL.support.TypeGenContext;
import wyvern.target.corewyvernIL.type.NominalType;
import wyvern.target.corewyvernIL.type.ValueType;
import wyvern.tools.errors.ErrorMessage;
import wyvern.tools.errors.FileLocation;
import wyvern.tools.errors.ToolError;
import wyvern.tools.typedAST.abs.CachingTypedAST;
import wyvern.tools.typedAST.core.declarations.DefDeclaration;
import wyvern.tools.typedAST.core.values.UnitVal;
import wyvern.tools.typedAST.interfaces.ApplyableValue;
import wyvern.tools.typedAST.interfaces.CoreAST;
import wyvern.tools.typedAST.interfaces.CoreASTVisitor;
import wyvern.tools.typedAST.interfaces.ExpressionAST;
import wyvern.tools.typedAST.interfaces.TypedAST;
import wyvern.tools.typedAST.interfaces.Value;
import wyvern.tools.typedAST.transformers.ExpressionWriter;
import wyvern.tools.typedAST.transformers.GenerationEnvironment;
import wyvern.tools.typedAST.transformers.ILWriter;
import wyvern.tools.types.ApplyableType;
import wyvern.tools.types.Environment;
import wyvern.tools.types.Type;
import wyvern.tools.types.extensions.Arrow;
import wyvern.tools.types.extensions.Intersection;
import wyvern.tools.util.EvaluationEnvironment;
import wyvern.tools.util.TreeWriter;

public class Application extends CachingTypedAST implements CoreAST {
	private ExpressionAST function;
	private ExpressionAST argument;
    private List<String> generics;

	public Application(TypedAST function, TypedAST argument, FileLocation location) {
        this(function, argument, location, null);
	}

    public Application(TypedAST function, TypedAST argument, FileLocation location, List<String> generics) {
		this.function = (ExpressionAST) function;
		this.argument = (ExpressionAST) argument;
		this.location = location;
        this.generics = (generics != null) ? generics : new LinkedList<String>();
	}

	@Override
	public void writeArgsToTree(TreeWriter writer) {
		writer.writeArgs(function, argument);
	}

	@Override
	protected Type doTypecheck(Environment env, Optional<Type> expected) {
		Type fnType = function.typecheck(env, Optional.empty());

		Type argument = null;
		if (fnType instanceof Arrow)
			argument = ((Arrow) fnType).getArgument();
		else if (fnType instanceof Intersection) {
			List<Type> args = fnType.getChildren().values().stream()
					.filter(tpe -> tpe instanceof Arrow).map(tpe->((Arrow)tpe).getArgument())
					.collect(Collectors.toList());
			argument = new Intersection(args);
		}
		if (this.argument != null)
			this.argument.typecheck(env, Optional.ofNullable(argument));
		
		if (!(fnType instanceof ApplyableType))
			reportError(TYPE_CANNOT_BE_APPLIED, this, fnType.toString());
		
		return ((ApplyableType)fnType).checkApplication(this, env);
	}

	public TypedAST getArgument() {
		return argument;
	}

	public TypedAST getFunction() {
		return function;
	}


	@Override
	public Value evaluate(EvaluationEnvironment env) {
		TypedAST lhs = function.evaluate(env);
		if (Globals.checkRuntimeTypes && !(lhs instanceof ApplyableValue))
			reportEvalError(VALUE_CANNOT_BE_APPLIED, lhs.toString(), this);
		ApplyableValue fnValue = (ApplyableValue) lhs;
		
		return fnValue.evaluateApplication(this, env);
	}

	@Override
	public void accept(CoreASTVisitor visitor) {
		visitor.visit(this);
	}
	@Override
	public Map<String, TypedAST> getChildren() {
		Hashtable<String, TypedAST> children = new Hashtable<>();
		children.put("function", function);
		children.put("argument", argument);
		return children;
	}

    @Override
    public void codegenToIL(GenerationEnvironment environment, ILWriter writer) {
        List<Expression> arguments;
        if (argument instanceof TupleObject) {
            arguments = Arrays.stream(((TupleObject) argument).getObjects()).map(a -> ExpressionWriter.generate(iw -> a.codegenToIL(environment, iw))).collect(Collectors.toList());
        } else {
            arguments = Arrays.asList(ExpressionWriter.generate(iw->argument.codegenToIL(environment, iw)));
        }
        if (function instanceof Invocation && ((Invocation) function).getArgument() == null) { // straight MethodCall
            writer.write(new MethodCall(ExpressionWriter.generate(iw -> function.codegenToIL(environment, iw)), ((Invocation) function).getOperationName(), arguments, this));
        }
        Expression expr = ExpressionWriter.generate(iw -> function.codegenToIL(environment, iw));
        writer.write(new MethodCall(expr, "call", arguments, this));
    }

    @Override
	public ExpressionAST doClone(Map<String, TypedAST> nc) {
		return new Application((ExpressionAST)nc.get("function"), (ExpressionAST)nc.get("argument"), location);
	}

	private FileLocation location;
	public FileLocation getLocation() {
		return this.location;
	}

    private ValueType getILTypeForGeneric(GenContext ctx, String genericName) {
        String objName = ctx.getContainerForTypeAbbrev(genericName);
        if (objName == null) {
            ToolError.reportError(ErrorMessage.TYPE_NOT_DEFINED, this, genericName);
        }
        return new NominalType(objName, genericName);
    }

    private void addGenericToArgList(String formalName, String generic, List<Expression> args, GenContext ctx) {
        String genericName = formalName.substring(DefDeclaration.GENERIC_PREFIX.length());
        ValueType vt = getILTypeForGeneric(ctx, generic);
        args.add(new wyvern.target.corewyvernIL.expression.New(new TypeDeclaration(genericName, vt, this.location)));
    }

    private int countFormalGenerics(List<FormalArg> formals) {
        int count = 0;

        for(FormalArg formal : formals) {
            String name = formal.getName();
            if(!name.startsWith(DefDeclaration.GENERIC_PREFIX)) {
                // We're hit the end of the generic args!
                break;
            }
            count++;
        }

        return count;
    }

    /**
        generateGenericArgs determined what the generic actuals are based on how many generics were provided and how many were expected by the formals.
    */
    private void generateGenericArgs(List<Expression> args, DefDeclType ddt, GenContext ctx) {
        List<FormalArg> formals = ddt.getFormalArgs();
        int count = countFormalGenerics(formals);
        if (count < this.generics.size()) {
            // then the number of actual generics is greater than the number of formal generics
            // this is not permitted.
            ToolError.reportError(ErrorMessage.EXTRA_GENERICS_AT_CALL_SITE, this);
        } else if(count == this.generics.size()) {
            // then we can simply add each of the actual generics to the argument's list
            for(int i = 0; i < count; i++) {
                String formalName = formals.get(i).getName();
                String generic = this.generics.get(i);
                addGenericToArgList(formalName, generic, args, ctx);    
            }
        } else {
            // this case executes when count > this.generics.size()
            // In this case, we can do type inference to determine what types have been elided

            // First, add any of the actual generics to the argument list.
            for(int i = 0; i < this.generics.size(); i++) {
                String formalName = formals.get(i).getName();
                String generic = this.generics.get(i);
                addGenericToArgList(formalName, generic, args, ctx);    
            }
            // Then, try to infer the type of the remaining generics

            // Collect the mapping from generic args to provided args
            Map<Integer, Integer> inferenceMap = ddt.genericMapping();

            for(int i = this.generics.size(); i < count; i++) {
                
                if(!inferenceMap.containsKey(i)) {
                    // then we can't infer the type
                    // TODO Missing generic at call site
                    ToolError.reportError(ErrorMessage.EXTRA_GENERICS_AT_CALL_SITE, this);
                }

                // formal position tells you where in the formals the argument that uses the generic is
                int formalPos = inferenceMap.get(i);
                // actual position tells you where in the actual argument list the type should be
                int actualPos = formalPos - count;
                if (this.argument instanceof TupleObject) {
                    ExpressionAST[] rawArgs = ((TupleObject) this.argument).getObjects();
                    if (formalPos == rawArgs.length) {
                        // then we're inferring from the result type
                    } else {
                        ExpressionAST inferArg = rawArgs[formalPos];
                        args.add(inferArg.generateIL(
                                ctx, formals.get(formalPos).getType()
                        ));
                    }
                } else if(this.argument instanceof UnitVal){
                    // uhhhhh?
                    // The arg is a unit value. We must be inferring from the result type
                } else {
                    // Then the arg must be a single element
                    if(actualPos != 0) {
                        // Inferring from a formal arg that doesn't exist
                        // TODO unless we're inferring from the result type.....
                        // ToolError
                    }
                    args.add(argument.generateIL(ctx, formals.get(0).getType()));
                }
            }
        }
    }
    
    private void generateILForTuples(List<FormalArg> formals, List<Expression> args, GenContext ctx) {
        ExpressionAST[] raw_args = ((TupleObject) this.argument).getObjects();
        if (formals.size() != raw_args.length + this.generics.size()) {
            ToolError.reportError(ErrorMessage.WRONG_NUMBER_OF_ARGUMENTS, this, ""+formals.size());
        }
        for (int i = 0; i < raw_args.length; i++) {
            ValueType expectedArgType = formals.get(i + this.generics.size()).getType();
            ExpressionAST ast = raw_args[i];
            // TODO: propagate types downward from formals
            args.add(ast.generateIL(ctx, expectedArgType));
        }
    }

	@Override
	public Expression generateIL(GenContext ctx, ValueType expectedType) {
		CallableExprGenerator exprGen = function.getCallableExpr(ctx);
        DefDeclType ddt = exprGen.getDeclType(ctx);
		List<FormalArg> formals = ddt.getFormalArgs();
        int offset;
		List<Expression> args = new LinkedList<Expression>();

        // Add generic arguments to the argslist
        generateGenericArgs(args, ddt, ctx);

        if (argument instanceof TupleObject) {
            generateILForTuples(formals, args, ctx);
        } else if (argument instanceof UnitVal) {
        	// leave args empty
        } else {
            // then there is only one argument, since len(actuals) is neither 0 nor > 1
            if (formals.size() != 1 + this.generics.size()) {
    			ToolError.reportError(ErrorMessage.WRONG_NUMBER_OF_ARGUMENTS, this, ""+formals.size());
            }
        	
    		// TODO: propagate types downward from formals
            // Add the single element to the arglist.
        	args.add(argument.generateIL(ctx, formals.get(0).getType()));
        }

		// generate the call
        return exprGen.genExprWithArgs(args, this);
	}
}
