package compomhp;

import soot.tagkit.Tag;

public class MyTag implements Tag {
    private final String name;

    public MyTag(String name) {
        this.name = name;
    }

    @Override
    public String getName() {
        return "MyTag";
    }

    @Override
    public byte[] getValue() {
        return name.getBytes();
    }

    public String getTagValue() {
        return name;
    }
}
