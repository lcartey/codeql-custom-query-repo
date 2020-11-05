import java
import semmle.code.java.security.XSS
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.dataflow.TaintTracking

class JaxRsMediaType extends Field {
  JaxRsMediaType() {
    getDeclaringType().hasQualifiedName("javax.ws.rs.core", "MediaType")
  }

  string getMediaTypeString() {
    // e.g. MediaType.TEXT_PLAIN => text/plain
    result = getName().toLowerCase().replaceAll("_", "/")
  }
}

/** An `@Produces` annotation that describes which MIME types can be produced by this resource. */
class JaxRsProducesAnnotation extends Annotation {
  JaxRsProducesAnnotation() { getType().hasQualifiedName("javax.ws.rs", "Produces") }

  /**
   * Gets a declared MIME type that can be produced by this resource.
   */
  string getADeclaredMimeType() {
    result = getAValue().(CompileTimeConstantExpr).getStringValue()
    or
    result = getAValue().(FieldAccess).getField().(JaxRsMediaType).getMediaTypeString()
  }
}

JaxRsProducesAnnotation getProducesAnnotation(JaxRsResourceMethod resourceMethod) {
  result = resourceMethod.getAnAnnotation()
}


/** Add the return values for the `text/plain` @Produces annotated methods as XSS sinks. */
class JaxRsPlainTextXssSink extends XssSink {
  JaxRsPlainTextXssSink() {
    exists(JaxRsResourceMethod resourceMethod, ReturnStmt rs |
      resourceMethod = any(JaxRsResourceClass resourceClass).getAResourceMethod() and
      rs.getEnclosingCallable() = resourceMethod and
      this.asExpr() = rs.getResult()
    |
      // No @Produces means that this resource method will return any MIME type specified
      // by the web client
      not exists(getProducesAnnotation(resourceMethod))
      or
      getProducesAnnotation(resourceMethod).getADeclaredMimeType() = "text/plain"
    )
  }
}

class JaxRsTaintSteps extends TaintTracking::AdditionalTaintStep {
  override predicate step(DataFlow::Node node1, DataFlow::Node node2) {
    // Response.ok() -> argument to return value
    exists(MethodAccess ma |
      ma.getMethod().getQualifiedName() = "Response.ok" and
      ma.getAnArgument() = node1.asExpr() and
      ma = node2.asExpr()
    )
    or
    exists(MethodAccess ma |
      ma.getMethod().getDeclaringType().getName() = "ResponseBuilder" and
      (
        // ResponseBuilder.x(y) -> qualifier to return value
        ma.getQualifier() = node1.asExpr()
        or
        // ResponseBuilder.x(y) -> argument to return value
        ma.getAnArgument() = node1.asExpr()
      ) and
      ma = node2.asExpr()
    )
  }
}
