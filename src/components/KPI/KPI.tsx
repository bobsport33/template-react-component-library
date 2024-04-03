import React, { useEffect } from "react";

import LinearProgress from "@mui/material/LinearProgress";
import { styled } from "@mui/material/styles";

interface KPIProps {
    id: string
}

const KPIWrapper = styled("div")`
    width: 23%;
    height: 13vh;

    .kpi {
        height: 100%;
        width: 100%;
        &__chart {
            height: 95%;
            width: 95%;
            animation: fadein 5s;
        }
    }
`;

const KPI = ({id} : KPIProps) => {
    // @ts-igonore
    const app = window.qlikApp;   

    const loadVisualization = (id: string) => {
        if (id === null) {
            return;
        }

        const splitId = id[0].split("|");
        app.visualization.get(splitId[0]).then((vis: any) => {
            vis.show(id[0]);
        });
    };

    useEffect(() => {
        loadVisualization(id);
    }, []);

    return (
        <KPIWrapper>
            <div className="kpi">
                <div id={id} className="kpi__chart">
                    <LinearProgress />
                </div>
            </div>
        </KPIWrapper>
    );
}

export default KPI
