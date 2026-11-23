package sjc.type.checker;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.ArrayAccess;
import org.eclipse.jdt.core.dom.ArrayCreation;
import org.eclipse.jdt.core.dom.ArrayInitializer;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.BooleanLiteral;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.ConditionalExpression;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.ExpressionStatement;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.NullLiteral;
import org.eclipse.jdt.core.dom.NumberLiteral;
import org.eclipse.jdt.core.dom.ParenthesizedExpression;
import org.eclipse.jdt.core.dom.PostfixExpression;
import org.eclipse.jdt.core.dom.PrefixExpression;
import org.eclipse.jdt.core.dom.PrimitiveType;
import org.eclipse.jdt.core.dom.ReturnStatement;
import org.eclipse.jdt.core.dom.SimpleType;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;
import org.eclipse.jdt.core.dom.WhileStatement;

import sjc.annotation.NonNull;
import sjc.annotation.NonNullElements;
import sjc.annotation.ReadOnly;
import sjc.annotation.ReadOnlyElements;
import sjc.symboltable.SymbolTable;
import sjc.type.ArrayType;
import sjc.type.BaseType;
import sjc.type.ClassType;
import sjc.type.NonPrimitiveType;
import sjc.type.NullType;
import sjc.type.Type;
import sjc.type.TypeFactory;
import sjc.util.Pair;

/**
 * This class is used to type check a StaticJava {@link CompilationUnit} with a
 * given {@link SymbolTable}.
 *
 */
public class TypeChecker {
  public static class Error extends RuntimeException {
    private static final long serialVersionUID = 5322515711212690043L;
    public final @NonNull @ReadOnly ASTNode node;
    public Error(@NonNull final ASTNode node, @NonNull final String message) {
      super(message);
      this.node = node;
    }
  }

  /** Visitor for type checking an ExtendedStaticJava compilation unit. */
  protected static class Visitor extends ASTVisitor {
    protected Map<ASTNode, Object> symbolMap;
    public Map<ASTNode, Type> resultTypeMap = new HashMap<>();
    public Map<Object, Pair<Type, List<Type>>> resultMethodTypeMap =
        new HashMap<>();
    protected TypeFactory tf;
    protected ArrayType stringArrayType;
    protected String className;
    protected Type methodReturnType, resultingType;
    protected @NonNullElements
    @ReadOnlyElements
    Map<String, TypeDeclaration> classMap;
    protected @NonNullElements
    @ReadOnlyElements
    Map<Pair<String, String>, FieldDeclaration> fieldMap;
    protected Visitor(final TypeFactory tf, final SymbolTable st) {
      this.tf = tf;
      this.symbolMap = st.symbolMap;
      this.stringArrayType =
          tf.getArrayType(tf.getClassType("java.lang.String"));
      this.classMap = st.classMap;
      this.fieldMap = st.fieldMap;
      for (final Pair<String, String> p : st.fieldMap.keySet()) {
        final FieldDeclaration fd = st.fieldMap.get(p);
        final Type t = convertType(fd, fd.getType());
        final ClassType ct = tf.getClassType(p.first);
        ct.fieldTypeMap.put(p.second, t);
      }
    }
    protected Type getResult() {
      Type t = resultingType;
      resultingType = null;
      return t;
    }
    protected void setResult(Expression n, Type t) {
      resultTypeMap.put(n, t);
      resultingType = t;
    }
    protected Type convertType(ASTNode n, Class c) {
      if (c == void.class)
        return tf.Void;
      if (c == boolean.class)
        return tf.Boolean;
      if (c == int.class)
        return tf.Int;
      if (c == String[].class)
        return stringArrayType;
      if (!c.isArray())
        return tf.getClassType(c.getName());
      return tf.getArrayType((BaseType) convertType(n, c.getComponentType()));
    }
    protected Type convertType(ASTNode n, org.eclipse.jdt.core.dom.Type t) {
      if (t instanceof PrimitiveType) {
        PrimitiveType.Code c = ((PrimitiveType) t).getPrimitiveTypeCode();
        if (c == PrimitiveType.BOOLEAN)
          return tf.Boolean;
        if (c == PrimitiveType.INT)
          return tf.Int;
        if (c == PrimitiveType.VOID)
          return tf.Void;
      }
      if (t instanceof SimpleType) {
        String s = ((SimpleType) t).getName().getFullyQualifiedName();
        if (classMap.containsKey(s))
          return tf.getClassType(s);
        if ("String".equals(s) || "java.lang.String".equals(s))
          return stringArrayType.baseType;
      }
      if (t instanceof org.eclipse.jdt.core.dom.ArrayType)
        return tf.getArrayType((BaseType) convertType(
            n, ((org.eclipse.jdt.core.dom.ArrayType) t).getElementType()));
      throw new Error(n, "Unexpected Type: '" + t + "'");
    }
    protected void dispose() {
      symbolMap = null;
      resultTypeMap = null;
      resultMethodTypeMap = null;
      tf = null;
      stringArrayType = null;
      className = null;
      methodReturnType = resultingType = null;
      classMap = null;
      fieldMap = null;
    }
    protected Method resolveMethod(
        MethodInvocation n, String c, String m, Type[] a) {
      try {
        Class[] p = new Class[a.length];
        for (int i = 0; i < a.length; i++) p[i] = convertClass(n, a[i]);
        Method r = Class.forName(c).getMethod(m, p);
        symbolMap.put(n, r);
        return r;
      } catch (Exception e) {
        throw new Error(n, "Unresolvable method \"" + c + "." + m + "\"");
      }
    }
    protected Class convertClass(ASTNode n, Type t) {
      if (t == tf.Void)
        return void.class;
      if (t == tf.Boolean)
        return boolean.class;
      if (t == tf.Int)
        return int.class;
      if (t == stringArrayType)
        return String[].class;
      if (t instanceof ClassType)
        try {
          return Class.forName(((ClassType) t).name);
        } catch (Exception e) {
        }
      throw new Error(n, "Unresolvable Type: '" + t + "'");
    }
    protected void typeCheckMethodInvocation(
        MethodInvocation n, String c, String m, Type[] a, Method d) {
      if (a.length != d.getParameterTypes().length)
        throw new Error(n,
            "Wrong number of arguments to invoke method \"" + m + "\" in \"" + n
                + "\"");
      List<Type> p = new ArrayList<>();
      for (int i = 0; i < a.length; i++) {
        Type t = convertType(n, d.getParameterTypes()[i]);
        if (!((a[i] instanceof NullType) && (t instanceof NonPrimitiveType))
            && t != a[i])
          throw new Error(
              n, "Type mismatch the " + i + " argument in \"" + n + "\"");
        p.add(t);
      }
      Type r = convertType(n, d.getReturnType());
      if (!resultMethodTypeMap.containsKey(d))
        resultMethodTypeMap.put(d, new Pair<Type, List<Type>>(r, p));
      setResult(n, r);
    }
    protected void typeCheckMethodInvocation(
        MethodInvocation n, String c, String m, Type[] a, MethodDeclaration d) {
      if (a.length != d.parameters().size())
        throw new Error(n,
            "Wrong number of arguments to invoke method \"" + m + "\" in \"" + n
                + "\"");
      for (int i = 0; i < a.length; i++)
        if (!((a[i] instanceof NullType)
                && (convertType(n, ((SingleVariableDeclaration) d.parameters()
                    .get(i)).getType()) instanceof NonPrimitiveType))
            && convertType(n,
                ((SingleVariableDeclaration) d.parameters().get(i)).getType())
            != a[i])
          throw new Error(
              n, "Type mismatch the " + i + " argument in \"" + n + "\"");
      setResult(n, convertType(n, d.getReturnType2()));
    }
    @Override
    public boolean visit(BooleanLiteral n) {
      setResult(n, tf.Boolean);
      return false;
    }
    @Override
    public boolean visit(NumberLiteral n) {
      setResult(n, tf.Int);
      return false;
    }
    /**
     * Type checks the given expression and returns its type.
     */
    protected Type typeOf(Expression e) {
      e.accept(this);
      return getResult();
    }

    /**
     * Determines whether a value of type rhs can be stored into type lhs.
     * Null can be assigned to any non-primitive (class or array) type.
     */
    protected boolean isAssignable(Type lhs, Type rhs) {
      return (lhs == rhs)
          || ((rhs instanceof NullType) && (lhs instanceof NonPrimitiveType));
    }

    /**
     * Returns the declared type of a variable declaration resolved by the
     * symbol table (local, parameter, or field).
     */
    protected Type getDeclaredType(ASTNode n, Object decl) {
      if (decl instanceof VariableDeclarationStatement)
        return convertType(n, ((VariableDeclarationStatement) decl).getType());
      if (decl instanceof SingleVariableDeclaration)
        return convertType(n, ((SingleVariableDeclaration) decl).getType());
      if (decl instanceof FieldDeclaration)
        return convertType(n, ((FieldDeclaration) decl).getType());

      throw new Error(n, "Unresolved variable: \"" + n + "\"");
    }

    @Override
    public boolean visit(ParenthesizedExpression n) {
      setResult(n, typeOf(n.getExpression()));
      return false;
    }
    @Override
    public boolean visit(FieldDeclaration n) {
      this.resultTypeMap.put(n, convertType(n, n.getType()));
      return false;
    }
    @Override
    public boolean visit(MethodDeclaration n) {
      List<Type> paramTypes = new ArrayList<>();
      for (Object o : n.parameters()) {
        SingleVariableDeclaration svd = (SingleVariableDeclaration) o;
        Type t = convertType(svd, svd.getType());
        this.resultTypeMap.put(svd, t);
        paramTypes.add(t);
      }

      this.methodReturnType = convertType(n, n.getReturnType2());
      this.resultMethodTypeMap.put(n,
          new Pair<Type, List<Type>>(this.methodReturnType, paramTypes));

      n.getBody().accept(this);

      this.methodReturnType = null;
      return false;
    }
    @Override
    public boolean visit(MethodInvocation n) {
      String m = n.getName().getIdentifier();
      Type[] a = new Type[n.arguments().size()];
      for (int i = 0; i < a.length; i++)
        a[i] = typeOf((Expression) n.arguments().get(i));

      Object decl = this.symbolMap.get(n);
      if (decl instanceof MethodDeclaration) {
        typeCheckMethodInvocation(n, this.className, m, a,
            (MethodDeclaration) decl);
        return false;
      }

      Expression e = n.getExpression();
      if (e == null)
        throw new Error(n, "Unresolvable method \"" + m + "\"");

      String c = e.toString();
      Method md = (decl instanceof Method)
          ? (Method) decl
          : resolveMethod(n, c, m, a);
      typeCheckMethodInvocation(n, c, m, a, md);
      return false;
    }
    @Override
    public boolean visit(SimpleName n) {
      setResult(n, getDeclaredType(n, this.symbolMap.get(n)));
      return false;
    }
    @Override
    public boolean visit(TypeDeclaration n) {
      this.className = n.getName().getIdentifier();
      this.resultTypeMap.put(n, this.tf.getClassType(this.className));

      for (FieldDeclaration fd : n.getFields()) fd.accept(this);

      for (MethodDeclaration md : n.getMethods()) md.accept(this);

      return false;
    }
    @Override
    public boolean visit(VariableDeclarationStatement n) {
      this.resultTypeMap.put(n, convertType(n, n.getType()));
      return false;
    }
    @Override
    public boolean visit(Assignment n) {
      Type lhs = typeOf(n.getLeftHandSide());
      Type rhs = typeOf(n.getRightHandSide());
      if (!isAssignable(lhs, rhs))
        throw new Error(n,
            "Type mismatch in \"" + n + "\": " + lhs + " = " + rhs);

      // assignments in StaticJava are statements, so no result type is set
      return false;
    }
    @Override
    public boolean visit(ExpressionStatement n) {
      n.getExpression().accept(this);

      // discard the expression's type; the statement has none
      getResult();
      return false;
    }
    @Override
    public boolean visit(InfixExpression n) {
      InfixExpression.Operator op = n.getOperator();
      Type lhs = typeOf(n.getLeftOperand());
      Type rhs = typeOf(n.getRightOperand());

      if ((op == InfixExpression.Operator.EQUALS)
          || (op == InfixExpression.Operator.NOT_EQUALS)) {
        boolean ok = ((lhs == rhs) && (lhs != this.tf.Void))
            || isAssignable(lhs, rhs) || isAssignable(rhs, lhs);
        if (!ok)
          throw new Error(n, "Type mismatch in \"" + n + "\": " + lhs + " "
              + op + " " + rhs);

        setResult(n, this.tf.Boolean);
        return false;
      }

      if ((op == InfixExpression.Operator.CONDITIONAL_AND)
          || (op == InfixExpression.Operator.CONDITIONAL_OR)) {
        checkOperands(n, lhs, rhs, this.tf.Boolean, "a boolean");

        setResult(n, this.tf.Boolean);
        return false;
      }

      if ((op == InfixExpression.Operator.LESS)
          || (op == InfixExpression.Operator.LESS_EQUALS)
          || (op == InfixExpression.Operator.GREATER)
          || (op == InfixExpression.Operator.GREATER_EQUALS)) {
        checkOperands(n, lhs, rhs, this.tf.Int, "an int");

        setResult(n, this.tf.Boolean);
        return false;
      }

      if ((op == InfixExpression.Operator.PLUS)
          || (op == InfixExpression.Operator.MINUS)
          || (op == InfixExpression.Operator.TIMES)
          || (op == InfixExpression.Operator.DIVIDE)
          || (op == InfixExpression.Operator.REMAINDER)
          || (op == InfixExpression.Operator.LEFT_SHIFT)
          || (op == InfixExpression.Operator.RIGHT_SHIFT_SIGNED)
          || (op == InfixExpression.Operator.RIGHT_SHIFT_UNSIGNED)) {
        checkOperands(n, lhs, rhs, this.tf.Int, "an int");

        setResult(n, this.tf.Int);
        return false;
      }

      throw new Error(n,
          "Unexpected operator \"" + op + "\" in \"" + n + "\"");
    }

    /**
     * Checks that both operands of a binary expression have the expected
     * type.
     */
    protected void checkOperands(InfixExpression n, Type lhs, Type rhs,
        Type expected, String expectedName) {
      if (lhs != expected)
        throw new Error(n, "Expecting " + expectedName
            + " type expression as the left-hand operand of \""
            + n.getOperator() + "\" in \"" + n + "\"");
      if (rhs != expected)
        throw new Error(n, "Expecting " + expectedName
            + " type expression as the right-hand operand of \""
            + n.getOperator() + "\" in \"" + n + "\"");
    }
    @Override
    public boolean visit(PrefixExpression n) {
      PrefixExpression.Operator op = n.getOperator();
      Type t = typeOf(n.getOperand());

      if (op == PrefixExpression.Operator.NOT) {
        if (t != this.tf.Boolean)
          throw new Error(n,
              "Expecting a boolean type expression as the operand of \"" + op
                  + "\" in \"" + n + "\"");

        setResult(n, this.tf.Boolean);
        return false;
      }

      if ((op == PrefixExpression.Operator.PLUS)
          || (op == PrefixExpression.Operator.MINUS)
          || (op == PrefixExpression.Operator.COMPLEMENT)) {
        if (t != this.tf.Int)
          throw new Error(n,
              "Expecting an int type expression as the operand of \"" + op
                  + "\" in \"" + n + "\"");

        setResult(n, this.tf.Int);
        return false;
      }

      throw new Error(n,
          "Unexpected operator \"" + op + "\" in \"" + n + "\"");
    }
    @Override
    public boolean visit(ReturnStatement n) {
      Expression e = n.getExpression();
      if (e == null) {
        if (this.methodReturnType != this.tf.Void)
          throw new Error(n, "Expecting " + this.methodReturnType
              + " return expression in \"" + n + "\"");
        return false;
      }

      if (this.methodReturnType == this.tf.Void)
        throw new Error(n, "Unexpected return's expression in \"" + n + "\"");

      if (!isAssignable(this.methodReturnType, typeOf(e)))
        throw new Error(n, "Expecting " + this.methodReturnType
            + " return expression in \"" + n + "\"");

      return false;
    }

    /**
     * Checks that the condition of a statement is a boolean expression.
     */
    protected void checkCondition(Expression e, String stmt) {
      if (typeOf(e) != this.tf.Boolean)
        throw new Error(e,
            "Expecting a boolean type expression as the condition of "
                + stmt + ": \"" + e + "\"");
    }
    @Override
    public boolean visit(IfStatement n) {
      checkCondition(n.getExpression(), "an if-statement");

      n.getThenStatement().accept(this);

      Statement elseStmt = n.getElseStatement();
      if (elseStmt != null) elseStmt.accept(this);

      return false;
    }
    @Override
    public boolean visit(WhileStatement n) {
      checkCondition(n.getExpression(), "a while-statement");

      n.getBody().accept(this);
      return false;
    }

    @Override
    public boolean visit(final ArrayAccess node) {
      Type arrayType = typeOf(node.getArray());
      if (!(arrayType instanceof ArrayType))
        throw new Error(node,
            "Expecting an array type expression in '" + node + "\"");

      if (typeOf(node.getIndex()) != this.tf.Int)
        throw new Error(node,
            "Expecting an int type for the index of '" + node + "\"");

      setResult(node, ((ArrayType) arrayType).baseType);
      return false;
    }

    @Override
    public boolean visit(final ArrayCreation node) {
      ArrayType t = (ArrayType) convertType(node, node.getType());

      for (Object o : node.dimensions())
        if (typeOf((Expression) o) != this.tf.Int)
          throw new Error(node,
              "Expecting an int type expression for the array length in '"
                  + node + "'");

      ArrayInitializer ai = node.getInitializer();
      if (ai != null) {
        for (int i = 0; i < ai.expressions().size(); i++) {
          Type et = typeOf((Expression) ai.expressions().get(i));
          if (!isAssignable(t.baseType, et))
            throw new Error(node, "Type mismatch in array initializer element "
                + i + " in '" + node + "': " + t.baseType + " : " + et);
        }
      }

      setResult(node, t);
      return false;
    }

    @Override
    public boolean visit(final ClassInstanceCreation node) {
      setResult(node, convertType(node, node.getType()));
      return false;
    }

    @Override
    public boolean visit(final ConditionalExpression node) {
      if (typeOf(node.getExpression()) != this.tf.Boolean)
        throw new Error(node,
            "Expecting a boolean type expression as the condition in '" + node
                + "\"");

      Type thenType = typeOf(node.getThenExpression());
      Type elseType = typeOf(node.getElseExpression());

      Type result;
      if (isAssignable(thenType, elseType)) result = thenType;
      else if (isAssignable(elseType, thenType)) result = elseType;
      else
        throw new Error(node, "Type mismatch for conditional expression '"
            + node + "\": " + thenType + " : " + elseType);

      setResult(node, result);
      return false;
    }

    @Override
    public boolean visit(final DoStatement node) {
      node.getBody().accept(this);

      checkCondition(node.getExpression(), "a while-statement");
      return false;
    }

    @Override
    public boolean visit(final FieldAccess node) {
      Type t = typeOf(node.getExpression());
      String name = node.getName().getIdentifier();
      if (!(t instanceof ClassType))
        throw new Error(node,
            "Expecting a class type expression for accessing field \"" + name
                + "\" in \"" + node + "\"");

      Type fieldType = ((ClassType) t).fieldTypeMap.get(name);
      if (fieldType == null)
        throw new Error(node,
            "Unresolvable field \"" + name + "\" in \"" + node + "\"");

      setResult(node, fieldType);
      return false;
    }

    @Override
    public boolean visit(final ForStatement node) {
      for (Object o : node.initializers()) ((ASTNode) o).accept(this);

      Expression e = node.getExpression();
      if (e != null) checkCondition(e, "a for-statement");

      for (Object o : node.updaters()) ((ASTNode) o).accept(this);

      node.getBody().accept(this);
      return false;
    }

    @Override
    public boolean visit(final NullLiteral node) {
      setResult(node, this.tf.Null);
      return false;
    }

    @Override
    public boolean visit(final PostfixExpression node) {
      node.getOperand().accept(this);
      final Type t = getResult();
      if (t != this.tf.Int) {
        throw new Error(node,
            "Expecting an int type expression as the operand of \'"
                + node.getOperator() + "\': \"" + node.getOperand() + "\"");
      }
      // no need to set the type result for postfix expressions since
      // postfix expressions in StaticJava are statements,
      // i.e., they are evaluated for their side-effects.
      return false;
    }

  }

  /**
   * Type checks an ExtendedStaticJava {@link CompilationUnit} with the given
   * {@link SymbolTable} and the given {@link TypeFactory}. It also
   * resolves {@link MethodInvocation} of library call (and put its mapping in
   * the {@link SymbolTable}).
   * 
   * @param tf
   *          The {@link TypeFactory}.
   * @param cu
   *          The StaticJava {@link CompilationUnit}.
   * @param symbolTable
   *          The {@link SymbolTable} of the {@link CompilationUnit}
   * @return The {@link TypeTable}.
   * @throws Error
   *           If the type checker encounter type error in the
   *           {@link CompilationUnit}.
   */
  public static @NonNull
  TypeTable check(@NonNull final TypeFactory tf,
      @NonNull final CompilationUnit cu,
      @NonNull final SymbolTable symbolTable) throws Error {
    assert (tf != null) && (cu != null) && (symbolTable != null);

    final Visitor v = new Visitor(tf, symbolTable);
    cu.accept(v);
    final TypeTable result = new TypeTable(v.resultTypeMap,
        v.resultMethodTypeMap);
    v.dispose();
    return result;
  }

  /**
   * Declared as protected to disallow creation of this object outside from the
   * methods of this class.
   */
  protected TypeChecker() {
  }
}
