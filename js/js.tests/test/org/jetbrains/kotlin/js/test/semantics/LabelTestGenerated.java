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

package org.jetbrains.kotlin.js.test.semantics;

import com.intellij.testFramework.TestDataPath;
import org.jetbrains.kotlin.test.JUnit3RunnerWithInners;
import org.jetbrains.kotlin.test.JetTestUtils;
import org.jetbrains.kotlin.test.TestMetadata;
import org.junit.runner.RunWith;

import java.io.File;
import java.util.regex.Pattern;

/** This class is generated by {@link org.jetbrains.kotlin.generators.tests.TestsPackage}. DO NOT MODIFY MANUALLY */
@SuppressWarnings("all")
@TestMetadata("js/js.translator/testData/labels/cases")
@TestDataPath("$PROJECT_ROOT")
@RunWith(JUnit3RunnerWithInners.class)
public class LabelTestGenerated extends AbstractLabelTest {
    public void testAllFilesPresentInCases() throws Exception {
        JetTestUtils.assertAllTestsPresentByMetadata(this.getClass(), new File("js/js.translator/testData/labels/cases"), Pattern.compile("^(.+)\\.kt$"), true);
    }

    @TestMetadata("labelWithVariableClashing.kt")
    public void testLabelWithVariableClashing() throws Exception {
        String fileName = JetTestUtils.navigationMetadata("js/js.translator/testData/labels/cases/labelWithVariableClashing.kt");
        doTest(fileName);
    }

    @TestMetadata("nestedLabels.kt")
    public void testNestedLabels() throws Exception {
        String fileName = JetTestUtils.navigationMetadata("js/js.translator/testData/labels/cases/nestedLabels.kt");
        doTest(fileName);
    }

    @TestMetadata("nestedLabelsInlinedClashing.kt")
    public void testNestedLabelsInlinedClashing() throws Exception {
        String fileName = JetTestUtils.navigationMetadata("js/js.translator/testData/labels/cases/nestedLabelsInlinedClashing.kt");
        doTest(fileName);
    }

    @TestMetadata("nestedLabelsInlinedClashingAtFunctionsWithClosure.kt")
    public void testNestedLabelsInlinedClashingAtFunctionsWithClosure() throws Exception {
        String fileName = JetTestUtils.navigationMetadata("js/js.translator/testData/labels/cases/nestedLabelsInlinedClashingAtFunctionsWithClosure.kt");
        doTest(fileName);
    }

    @TestMetadata("siblingLabels.kt")
    public void testSiblingLabels() throws Exception {
        String fileName = JetTestUtils.navigationMetadata("js/js.translator/testData/labels/cases/siblingLabels.kt");
        doTest(fileName);
    }

    @TestMetadata("siblingLabelsInlined.kt")
    public void testSiblingLabelsInlined() throws Exception {
        String fileName = JetTestUtils.navigationMetadata("js/js.translator/testData/labels/cases/siblingLabelsInlined.kt");
        doTest(fileName);
    }

    @TestMetadata("siblingLabelsInlinedClashing.kt")
    public void testSiblingLabelsInlinedClashing() throws Exception {
        String fileName = JetTestUtils.navigationMetadata("js/js.translator/testData/labels/cases/siblingLabelsInlinedClashing.kt");
        doTest(fileName);
    }

    @TestMetadata("simpleLabel.kt")
    public void testSimpleLabel() throws Exception {
        String fileName = JetTestUtils.navigationMetadata("js/js.translator/testData/labels/cases/simpleLabel.kt");
        doTest(fileName);
    }

    @TestMetadata("simpleLabelInlined.kt")
    public void testSimpleLabelInlined() throws Exception {
        String fileName = JetTestUtils.navigationMetadata("js/js.translator/testData/labels/cases/simpleLabelInlined.kt");
        doTest(fileName);
    }
}
