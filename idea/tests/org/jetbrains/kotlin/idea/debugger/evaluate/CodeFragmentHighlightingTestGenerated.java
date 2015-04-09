/*
 * Copyright 2010-2015 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.jetbrains.kotlin.idea.debugger.evaluate;

import com.intellij.testFramework.TestDataPath;
import org.jetbrains.kotlin.test.JUnit3RunnerWithInners;
import org.jetbrains.kotlin.test.JetTestUtils;
import org.jetbrains.kotlin.test.TestMetadata;
import org.junit.runner.RunWith;

import java.io.File;
import java.util.regex.Pattern;

/** This class is generated by {@link org.jetbrains.kotlin.generators.tests.TestsPackage}. DO NOT MODIFY MANUALLY */
@SuppressWarnings("all")
@RunWith(JUnit3RunnerWithInners.class)
public class CodeFragmentHighlightingTestGenerated extends AbstractCodeFragmentHighlightingTest {
    @TestMetadata("idea/testData/checker/codeFragments")
    @TestDataPath("$PROJECT_ROOT")
    @RunWith(JUnit3RunnerWithInners.class)
    public static class CodeFragments extends AbstractCodeFragmentHighlightingTest {
        public void testAllFilesPresentInCodeFragments() throws Exception {
            JetTestUtils.assertAllTestsPresentByMetadata(this.getClass(), new File("idea/testData/checker/codeFragments"), Pattern.compile("^(.+)\\.kt$"), false);
        }

        @TestMetadata("binaryExpression.kt")
        public void testBinaryExpression() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/binaryExpression.kt");
            doTest(fileName);
        }

        @TestMetadata("blockCodeFragment.kt")
        public void testBlockCodeFragment() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/blockCodeFragment.kt");
            doTest(fileName);
        }

        @TestMetadata("callExpression.kt")
        public void testCallExpression() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/callExpression.kt");
            doTest(fileName);
        }

        @TestMetadata("classHeader.kt")
        public void testClassHeader() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/classHeader.kt");
            doTest(fileName);
        }

        @TestMetadata("classHeaderWithTypeArguments.kt")
        public void testClassHeaderWithTypeArguments() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/classHeaderWithTypeArguments.kt");
            doTest(fileName);
        }

        @TestMetadata("contextElementAsStatement.kt")
        public void testContextElementAsStatement() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/contextElementAsStatement.kt");
            doTest(fileName);
        }

        @TestMetadata("localVariables.kt")
        public void testLocalVariables() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/localVariables.kt");
            doTest(fileName);
        }

        @TestMetadata("localVariablesOnReturn.kt")
        public void testLocalVariablesOnReturn() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/localVariablesOnReturn.kt");
            doTest(fileName);
        }

        @TestMetadata("privateFunArgumentsResolve.kt")
        public void testPrivateFunArgumentsResolve() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/privateFunArgumentsResolve.kt");
            doTest(fileName);
        }

        @TestMetadata("privateFunTypeArguments.kt")
        public void testPrivateFunTypeArguments() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/privateFunTypeArguments.kt");
            doTest(fileName);
        }

        @TestMetadata("privateMember.kt")
        public void testPrivateMember() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/privateMember.kt");
            doTest(fileName);
        }

        @TestMetadata("protectedMember.kt")
        public void testProtectedMember() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/protectedMember.kt");
            doTest(fileName);
        }

        @TestMetadata("simpleNameExpression.kt")
        public void testSimpleNameExpression() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/simpleNameExpression.kt");
            doTest(fileName);
        }

        @TestMetadata("smartCasts.kt")
        public void testSmartCasts() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/smartCasts.kt");
            doTest(fileName);
        }
    }

    @TestMetadata("idea/testData/checker/codeFragments/imports")
    @TestDataPath("$PROJECT_ROOT")
    @RunWith(JUnit3RunnerWithInners.class)
    public static class Imports extends AbstractCodeFragmentHighlightingTest {
        public void testAllFilesPresentInImports() throws Exception {
            JetTestUtils.assertAllTestsPresentByMetadata(this.getClass(), new File("idea/testData/checker/codeFragments/imports"), Pattern.compile("^(.+)\\.kt$"), true);
        }

        @TestMetadata("hashMap.kt")
        public void testHashMap() throws Exception {
            String fileName = JetTestUtils.navigationMetadata("idea/testData/checker/codeFragments/imports/hashMap.kt");
            doTestWithImport(fileName);
        }
    }
}
