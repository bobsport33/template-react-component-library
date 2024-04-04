import Button from "../components/Button/Button";

export default {
    title: "Components/Button",
    component: Button,
    argTypes: { onClick: { action: "onClick" } },
};

export const Red = {
    args: {
        label: "Press",
        backgroundColor: "red",
    },
};
export const Blue = {
    args: {
        label: "Press me",
        backgroundColor: "blue",
    },
};
