/*
 * Copyright 2010-2018 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.backend.jvm.lower

import org.jetbrains.kotlin.backend.common.ClassLoweringPass
import org.jetbrains.kotlin.backend.common.FileLoweringPass
import org.jetbrains.kotlin.backend.common.lower.replaceThisByStaticReference
import org.jetbrains.kotlin.backend.common.phaser.makeIrFilePhase
import org.jetbrains.kotlin.backend.jvm.JvmBackendContext
import org.jetbrains.kotlin.backend.jvm.codegen.isJvmInterface
import org.jetbrains.kotlin.backend.jvm.ir.allFieldsAreJvmField
import org.jetbrains.kotlin.descriptors.Visibilities
import org.jetbrains.kotlin.ir.IrStatement
import org.jetbrains.kotlin.ir.declarations.*
import org.jetbrains.kotlin.ir.declarations.impl.IrAnonymousInitializerImpl
import org.jetbrains.kotlin.ir.declarations.impl.IrVariableImpl
import org.jetbrains.kotlin.ir.descriptors.WrappedVariableDescriptor
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.expressions.impl.IrGetFieldImpl
import org.jetbrains.kotlin.ir.expressions.impl.IrGetValueImpl
import org.jetbrains.kotlin.ir.expressions.impl.IrSetFieldImpl
import org.jetbrains.kotlin.ir.symbols.impl.IrAnonymousInitializerSymbolImpl
import org.jetbrains.kotlin.ir.symbols.impl.IrVariableSymbolImpl
import org.jetbrains.kotlin.ir.util.deepCopyWithSymbols
import org.jetbrains.kotlin.ir.util.isObject
import org.jetbrains.kotlin.ir.visitors.IrElementTransformerVoid

internal val moveOrCopyCompanionObjectFieldsPhase = makeIrFilePhase(
    ::MoveOrCopyCompanionObjectFieldsLowering,
    name = "MoveOrCopyCompanionObjectFields",
    description = "Move and/or copy companion object fields to static fields of companion's owner"
)

internal val replaceStaticFieldCallSitesPhase = makeIrFilePhase(
    ::ReplaceStaticFieldCallSites,
    name = "ReplaceStaticFieldCallSites",
    description = "Remove receiver at call sites of static fields"
)

private class MoveOrCopyCompanionObjectFieldsLowering(val context: JvmBackendContext) : ClassLoweringPass {
    override fun lower(irClass: IrClass) {
        if (irClass.isObject && !irClass.isCompanion && irClass.visibility != Visibilities.LOCAL) {
            handleObject(irClass)
        } else {
            handleClass(irClass)
            if (irClass.isJvmInterface)
                copyConsts(irClass)
        }
    }

    private fun handleObject(irObject: IrClass) {
        irObject.declarations.replaceAll {
            when (it) {
                is IrProperty -> {
                    // The field is not actually moved, just replaced by a static field
                    moveOrCopyPropertyFieldToStaticParent(it, irObject, irObject)
                    it
                }
                is IrAnonymousInitializer -> moveAnonymousInitializerToStaticParent(it, irObject, irObject)
                else -> it
            }
        }
    }

    private fun handleClass(irClass: IrClass) {
        val companion = irClass.declarations.find {
            it is IrClass && it.isCompanion
        } as IrClass? ?: return

        // We don't move fields to interfaces unless all fields are annotated with @JvmField.
        // It is an error to annotate only some of the fields of an interface companion with @JvmField.
        val newParent = if (irClass.isJvmInterface && !companion.allFieldsAreJvmField()) companion else irClass

        val newDeclarations = companion.declarations.mapNotNull {
            when (it) {
                is IrProperty ->
                    moveOrCopyPropertyFieldToStaticParent(it, companion, newParent)
                is IrAnonymousInitializer ->
                    moveAnonymousInitializerToStaticParent(it, companion, newParent)
                else ->
                    null
            }
        }

        // Move declarations to parent if required
        if (newParent !== companion) {
            companion.declarations.removeAll { it is IrAnonymousInitializer }
            newParent.declarations += newDeclarations
        }
    }

    private fun copyConsts(irClass: IrClass) {
        val companion = irClass.declarations.find {
            it is IrClass && it.isCompanion
        } as IrClass? ?: return
        companion.declarations.filter { it is IrProperty && it.isConst && it.hasPublicVisibility }
            .mapNotNullTo(irClass.declarations) { moveOrCopyPropertyFieldToStaticParent(it as IrProperty, companion, irClass, copy = true) }
    }

    private val IrProperty.hasPublicVisibility: Boolean
        get() = !Visibilities.isPrivate(visibility) && visibility != Visibilities.PROTECTED

    private fun moveOrCopyPropertyFieldToStaticParent(
        irProperty: IrProperty,
        propertyParent: IrClass,
        fieldParent: IrClass,
        copy: Boolean = false
    ): IrField? {
        val newField = context.declarationFactory.copyFieldIfNeeded(irProperty, fieldParent, isStatic = true) ?: return null

        val oldInitializer = irProperty.backingField?.initializer
        if (oldInitializer != null) {
            newField.initializer = oldInitializer
                .replaceThisByStaticReference(context, propertyParent, propertyParent.thisReceiver!!)
                .deepCopyWithSymbols(newField) as IrExpressionBody
        }

        if (!copy) {
            irProperty.backingField = newField
            newField.correspondingPropertySymbol = irProperty.symbol
        }

        return newField
    }

    private fun moveAnonymousInitializerToStaticParent(
        oldInitializer: IrAnonymousInitializer,
        oldParent: IrClass,
        newParent: IrClass
    ): IrAnonymousInitializer =
        with(oldInitializer) {
            IrAnonymousInitializerImpl(
                startOffset, endOffset, origin, IrAnonymousInitializerSymbolImpl(newParent.symbol),
                isStatic = true
            ).apply {
                parent = newParent
                body = oldInitializer.body.transferToNewParent(oldParent, newParent)
            }
        }

    private fun IrBlockBody.transferToNewParent(oldParent: IrClass, newParent: IrClass): IrBlockBody {
        val objectInstanceField = context.declarationFactory.getFieldForObjectInstance(oldParent)
        return transform(
            data = null,
            transformer = object : IrElementTransformerVoid() {
                val variableMap = mutableMapOf<IrVariable, IrVariable>()

                override fun visitVariable(declaration: IrVariable): IrStatement {
                    if (declaration.parent == oldParent) {
                        val newDescriptor = WrappedVariableDescriptor(declaration.descriptor.annotations, declaration.descriptor.source)
                        val newVariable = IrVariableImpl(
                            declaration.startOffset, declaration.endOffset,
                            declaration.origin, IrVariableSymbolImpl(newDescriptor),
                            declaration.name, declaration.type, declaration.isVar, declaration.isConst, declaration.isLateinit
                        ).apply {
                            newDescriptor.bind(this)
                            parent = newParent
                            initializer = declaration.initializer
                            annotations.addAll(declaration.annotations)
                        }
                        variableMap[declaration] = newVariable
                        return super.visitVariable(newVariable)
                    }
                    return super.visitVariable(declaration)
                }

                override fun visitGetValue(expression: IrGetValue): IrExpression {
                    if (expression.symbol.owner == oldParent.thisReceiver) {
                        return IrGetFieldImpl(
                            expression.startOffset, expression.endOffset,
                            objectInstanceField.symbol,
                            expression.type
                        )
                    }
                    variableMap[expression.symbol.owner]?.let { newVariable ->
                        return IrGetValueImpl(
                            expression.startOffset, expression.endOffset,
                            expression.type,
                            newVariable.symbol,
                            expression.origin
                        )
                    }
                    return super.visitGetValue(expression)
                }
            }) as IrBlockBody
    }
}

private class ReplaceStaticFieldCallSites(private val context: JvmBackendContext) : FileLoweringPass, IrElementTransformerVoid() {
    override fun lower(irFile: IrFile) {
        irFile.transformChildrenVoid()
    }

    override fun visitGetField(expression: IrGetField): IrExpression {
        val newSymbol = context.declarationFactory.mapField(expression.symbol)?.takeIf { it.owner.isStatic }
            ?: return super.visitGetField(expression)

        return with(expression) {
            IrGetFieldImpl(startOffset, endOffset, newSymbol, type, /* receiver = */ null, origin, superQualifierSymbol)
        }
    }

    override fun visitSetField(expression: IrSetField): IrExpression {
        val newSymbol = context.declarationFactory.mapField(expression.symbol)?.takeIf { it.owner.isStatic }
            ?: return super.visitSetField(expression)

        return with(expression) {
            IrSetFieldImpl(
                startOffset, endOffset, newSymbol, /* receiver = */ null, visitExpression(value), type, origin, superQualifierSymbol
            )
        }
    }
}
